/*-------------------------------------------------------------------------
 *
 * nodeHash.c
 *	  Routines to hash relations for hashjoin
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeHash.c,v 1.96.2.2 2005/11/23 20:28:04 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *		MultiExecHash	- generate an in-memory hash table of the relation
 *		ExecInitHash	- initialize node and subnodes
 *		ExecEndHash		- shutdown node and subnodes
 */
#include "postgres.h"

#include "executor/execdebug.h"
#include "executor/hashjoin.h"
#include "executor/instrument.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "miscadmin.h"
#include "parser/parse_expr.h"
#include "utils/memutils.h"
#include "utils/lsyscache.h"


static void ExecHashIncreaseNumBatches(HashJoinTable hashtable);


/* ----------------------------------------------------------------
 *		ExecHash
 *
 *		stub for pro forma compliance
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecHash(HashState *node)
{
	elog(ERROR, "Hash node does not support ExecProcNode call convention");
	return NULL;
}

/* ----------------------------------------------------------------
 *		MultiExecHash
 *
 *		build hash table for hashjoin, doing partitioning if more
 *		than one batch is required.
 * ----------------------------------------------------------------
 */
Node *
MultiExecHash(HashState *node)
{
	PlanState  *outerNode;
	List	   *hashkeys;
	HashJoinTable hashtable;
	TupleTableSlot *slot;
	ExprContext *econtext;
	uint32		hashvalue;

	/* must provide our own instrumentation support */
	if (node->ps.instrument)
		InstrStartNode(node->ps.instrument);

	/*
	 * get state info from node
	 */
	outerNode = outerPlanState(node);
	hashtable = node->hashtable;

	/*
	 * set expression context
	 */
	hashkeys = node->hashkeys;
	econtext = node->ps.ps_ExprContext;

	/*
	 * get all inner tuples and insert into the hash table (or temp files)
	 */
	for (;;)
	{
		slot = ExecProcNode(outerNode);
		if (TupIsNull(slot))
			break;
		hashtable->totalTuples += 1;
		/* We have to compute the hash value */
		econtext->ecxt_innertuple = slot;
		hashvalue = ExecHashGetHashValue(hashtable, econtext, hashkeys);
		ExecHashTableInsert(hashtable, ExecFetchSlotTuple(slot), hashvalue);
	}

	/* must provide our own instrumentation support */
	if (node->ps.instrument)
		InstrStopNodeMulti(node->ps.instrument, hashtable->totalTuples);

	/*
	 * We do not return the hash table directly because it's not a subtype of
	 * Node, and so would violate the MultiExecProcNode API.  Instead, our
	 * parent Hashjoin node is expected to know how to fish it out of our node
	 * state.  Ugly but not really worth cleaning up, since Hashjoin knows
	 * quite a bit more about Hash besides that.
	 */
	return NULL;
}

/* ----------------------------------------------------------------
 *		ExecInitHash
 *
 *		Init routine for Hash node
 * ----------------------------------------------------------------
 */
HashState *
ExecInitHash(Hash *node, EState *estate)
{
	HashState  *hashstate;

	SO_printf("ExecInitHash: initializing hash node\n");

	/*
	 * create state structure
	 */
	hashstate = makeNode(HashState);
	hashstate->ps.plan = (Plan *) node;
	hashstate->ps.state = estate;
	hashstate->hashtable = NULL;
	hashstate->hashkeys = NIL;	/* will be set by parent HashJoin */

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hashstate->ps);

#define HASH_NSLOTS 1

	/*
	 * initialize our result slot
	 */
	ExecInitResultTupleSlot(estate, &hashstate->ps);

	/*
	 * initialize child expressions
	 */
	hashstate->ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->plan.targetlist,
					 (PlanState *) hashstate);
	hashstate->ps.qual = (List *)
		ExecInitExpr((Expr *) node->plan.qual,
					 (PlanState *) hashstate);

	/*
	 * initialize child nodes
	 */
	outerPlanState(hashstate) = ExecInitNode(outerPlan(node), estate);

	/*
	 * initialize tuple type. no need to initialize projection info because
	 * this node doesn't do projections
	 */
	ExecAssignResultTypeFromTL(&hashstate->ps);
	hashstate->ps.ps_ProjInfo = NULL;

	return hashstate;
}

int
ExecCountSlotsHash(Hash *node)
{
	return ExecCountSlotsNode(outerPlan(node)) +
		ExecCountSlotsNode(innerPlan(node)) +
		HASH_NSLOTS;
}

/* ---------------------------------------------------------------
 *		ExecEndHash
 *
 *		clean up routine for Hash node
 * ----------------------------------------------------------------
 */
void
ExecEndHash(HashState *node)
{
	PlanState  *outerPlan;

	/*
	 * free exprcontext
	 */
	ExecFreeExprContext(&node->ps);

	/*
	 * shut down the subplan
	 */
	outerPlan = outerPlanState(node);
	ExecEndNode(outerPlan);
}


/* ----------------------------------------------------------------
 *		ExecHashTableCreate
 *
 *		create an empty hashtable data structure for hashjoin.
 * ----------------------------------------------------------------
 */
HashJoinTable
ExecHashTableCreate(Hash *node, List *hashOperators)
{
	HashJoinTable hashtable;
	Plan	   *outerNode;
	int			nbuckets;
	int			nbatch;
	int			nkeys;
	int			i;
	ListCell   *ho;
	MemoryContext oldcxt;

	/*
	 * Get information about the size of the relation to be hashed (it's the
	 * "outer" subtree of this node, but the inner relation of the hashjoin).
	 * Compute the appropriate size of the hash table.
	 */
	outerNode = outerPlan(node);

	ExecChooseHashTableSize(outerNode->plan_rows, outerNode->plan_width,
							&nbuckets, &nbatch);

#ifdef HJDEBUG
	printf("nbatch = %d, nbuckets = %d\n", nbatch, nbuckets);
#endif

	/*
	 * Initialize the hash table control block.
	 *
	 * The hashtable control block is just palloc'd from the executor's
	 * per-query memory context.
	 */
	hashtable = (HashJoinTable) palloc(sizeof(HashJoinTableData));
	hashtable->nbuckets = nbuckets;
	hashtable->buckets = NULL;
	hashtable->nbatch = nbatch;
	hashtable->curbatch = 0;
	hashtable->nbatch_original = nbatch;
	hashtable->nbatch_outstart = nbatch;
	hashtable->growEnabled = true;
	hashtable->totalTuples = 0;
	hashtable->innerBatchFile = NULL;
	hashtable->outerBatchFile = NULL;
	hashtable->spaceUsed = 0;
	hashtable->spaceAllowed = work_mem * 1024L;

	/*
	 * Get info about the hash functions to be used for each hash key.
	 */
	nkeys = list_length(hashOperators);
	hashtable->hashfunctions = (FmgrInfo *) palloc(nkeys * sizeof(FmgrInfo));
	i = 0;
	foreach(ho, hashOperators)
	{
		Oid			hashfn;

		hashfn = get_op_hash_function(lfirst_oid(ho));
		if (!OidIsValid(hashfn))
			elog(ERROR, "could not find hash function for hash operator %u",
				 lfirst_oid(ho));
		fmgr_info(hashfn, &hashtable->hashfunctions[i]);
		i++;
	}

	/*
	 * Create temporary memory contexts in which to keep the hashtable working
	 * storage.  See notes in executor/hashjoin.h.
	 */
	hashtable->hashCxt = AllocSetContextCreate(CurrentMemoryContext,
											   "HashTableContext",
											   ALLOCSET_DEFAULT_MINSIZE,
											   ALLOCSET_DEFAULT_INITSIZE,
											   ALLOCSET_DEFAULT_MAXSIZE);

	hashtable->batchCxt = AllocSetContextCreate(hashtable->hashCxt,
												"HashBatchContext",
												ALLOCSET_DEFAULT_MINSIZE,
												ALLOCSET_DEFAULT_INITSIZE,
												ALLOCSET_DEFAULT_MAXSIZE);

	/* Allocate data that will live for the life of the hashjoin */

	oldcxt = MemoryContextSwitchTo(hashtable->hashCxt);

	if (nbatch > 1)
	{
		/*
		 * allocate and initialize the file arrays in hashCxt
		 */
		hashtable->innerBatchFile = (BufFile **)
			palloc0(nbatch * sizeof(BufFile *));
		hashtable->outerBatchFile = (BufFile **)
			palloc0(nbatch * sizeof(BufFile *));
		/* The files will not be opened until needed... */
	}

	/*
	 * Prepare context for the first-scan space allocations; allocate the
	 * hashbucket array therein, and set each bucket "empty".
	 */
	MemoryContextSwitchTo(hashtable->batchCxt);

	hashtable->buckets = (HashJoinTuple *)
		palloc0(nbuckets * sizeof(HashJoinTuple));

	MemoryContextSwitchTo(oldcxt);

	return hashtable;
}


/*
 * Compute appropriate size for hashtable given the estimated size of the
 * relation to be hashed (number of rows and average row width).
 *
 * This is exported so that the planner's costsize.c can use it.
 */

/* Target bucket loading (tuples per bucket) */
#define NTUP_PER_BUCKET			10

/* Prime numbers that we like to use as nbuckets values */
static const int hprimes[] = {
	1033, 2063, 4111, 8219, 16417, 32779, 65539, 131111,
	262151, 524341, 1048589, 2097211, 4194329, 8388619, 16777289, 33554473,
	67108913, 134217773, 268435463, 536870951, 1073741831
};

void
ExecChooseHashTableSize(double ntuples, int tupwidth,
						int *numbuckets,
						int *numbatches)
{
	int			tupsize;
	double		inner_rel_bytes;
	long		hash_table_bytes;
	int			nbatch;
	int			nbuckets;
	int			i;

	/* Force a plausible relation size if no info */
	if (ntuples <= 0.0)
		ntuples = 1000.0;

	/*
	 * Estimate tupsize based on footprint of tuple in hashtable... note this
	 * does not allow for any palloc overhead.	The manipulations of spaceUsed
	 * don't count palloc overhead either.
	 */
	tupsize = MAXALIGN(sizeof(HashJoinTupleData)) +
		MAXALIGN(sizeof(HeapTupleHeaderData)) +
		MAXALIGN(tupwidth);
	inner_rel_bytes = ntuples * tupsize;

	/*
	 * Target in-memory hashtable size is work_mem kilobytes.
	 */
	hash_table_bytes = work_mem * 1024L;

	/*
	 * Set nbuckets to achieve an average bucket load of NTUP_PER_BUCKET when
	 * memory is filled.  Set nbatch to the smallest power of 2 that appears
	 * sufficient.
	 * (hybrid hash join). For CSI3130, we disable multiple batches
	 */

	if (inner_rel_bytes > hash_table_bytes)
	{
		/* We'll need multiple batches */
		long		lbuckets;
		/* CSI3130: Even if the table is large, we will still force a sinle batch */
		
		lbuckets = (hash_table_bytes / tupsize) / NTUP_PER_BUCKET;
		lbuckets = Min(lbuckets, INT_MAX);
		nbuckets = (int) lbuckets;
        
	}
	else
	{
		/* We expect the hashtable to fit in memory */
		double		dbuckets;

		dbuckets = ceil(ntuples / NTUP_PER_BUCKET);
		dbuckets = Min(dbuckets, INT_MAX);
		nbuckets = (int) dbuckets;
	}

	/*
	 * We want nbuckets to be prime so as to avoid having bucket and batch
	 * numbers depend on only some bits of the hash code.  Choose the next
	 * larger prime from the list in hprimes[].  (This also enforces that
	 * nbuckets is not very small, by the simple expedient of not putting any
	 * very small entries in hprimes[].)
	 */
	for (i = 0; i < (int) lengthof(hprimes); i++)
	{
		if (hprimes[i] >= nbuckets)
		{
			nbuckets = hprimes[i];
			break;
		}
	}

	*numbuckets = nbuckets;

	/* CSI3130: Disable multiple batches by forcing exactly one batch */
	nbatch = 1;
	*numbatches = nbatch;
}


/* ----------------------------------------------------------------
 *		ExecHashTableDestroy
 *
 *		destroy a hash table
 * ----------------------------------------------------------------
 */
void
ExecHashTableDestroy(HashJoinTable hashtable)
{
	/* CSI3130: batching disabled – no temp batch files to close here.
	 * nbatch is always 1 and innerBatchFile/outerBatchFile remain NULL.
	 */

	/* Release working memory (batchCxt is a child, so it goes away too) */
	MemoryContextDelete(hashtable->hashCxt);

	/* And drop the control block */
	pfree(hashtable);
}

/* ----------------------------------------------------------------
 * ExecHashIncreaseNumBatches
 *
 * CSI3130: Batching disabled.
 * PostgreSQL normally increases the number of batches when the hash
 * table grows too large. For this assignment, we assume the entire
 * hash table fits in memory and we never create additional batches.
 * Therefore, this function is now an intentional no-op.
 * ----------------------------------------------------------------
 */
static void
ExecHashIncreaseNumBatches(HashJoinTable hashtable)
{
    /* CSI3130: batching disabled – do nothing */
    return;
}


void
ExecHashTableInsert(HashJoinTable hashtable,
					HeapTuple tuple,
					uint32 hashvalue)
{
	int			bucketno;
	int			batchno;

	ExecHashGetBucketAndBatch(hashtable, hashvalue,
							  &bucketno, &batchno);

	/*
	 * decide whether to put the tuple in the hash table or a temp file
	 */
	/* CSI3130: batching disabled - we always use a single in-memory batch.
	 * batchno should always be 0 and equal to curbatch (also 0) */

		HashJoinTuple hashTuple;
		int			hashTupleSize;

		hashTupleSize = MAXALIGN(sizeof(HashJoinTupleData)) + tuple->t_len;
		hashTuple = (HashJoinTuple) MemoryContextAlloc(hashtable->batchCxt,
													   hashTupleSize);
		hashTuple->hashvalue = hashvalue;
		memcpy((char *) &hashTuple->htup,
			   (char *) tuple,
			   sizeof(hashTuple->htup));
		hashTuple->htup.t_datamcxt = hashtable->batchCxt;
		hashTuple->htup.t_data = (HeapTupleHeader)
			(((char *) hashTuple) + MAXALIGN(sizeof(HashJoinTupleData)));

		memcpy((char *) hashTuple->htup.t_data,
			   (char *) tuple->t_data,
			   tuple->t_len);
		/* Insert at the head of the bucket's chain */	   
		hashTuple->next = hashtable->buckets[bucketno];
		hashtable->buckets[bucketno] = hashTuple;
		
		/* CSI3130: We still track spaceUsed, but we no longer create more batches. */
		hashtable->spaceUsed += hashTupleSize;
		
							
}

/*
 * ExecHashGetHashValue
 *		Compute the hash value for a tuple
 *
 * The tuple to be tested must be in either econtext->ecxt_outertuple or
 * econtext->ecxt_innertuple.  Vars in the hashkeys expressions reference
 * either OUTER or INNER.
 */
uint32
ExecHashGetHashValue(HashJoinTable hashtable,
					 ExprContext *econtext,
					 List *hashkeys)
{
	uint32		hashkey = 0;
	ListCell   *hk;
	int			i = 0;
	MemoryContext oldContext;

	/*
	 * We reset the eval context each time to reclaim any memory leaked in the
	 * hashkey expressions.
	 */
	ResetExprContext(econtext);

	oldContext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

	foreach(hk, hashkeys)
	{
		ExprState  *keyexpr = (ExprState *) lfirst(hk);
		Datum		keyval;
		bool		isNull;

		/* rotate hashkey left 1 bit at each step */
		hashkey = (hashkey << 1) | ((hashkey & 0x80000000) ? 1 : 0);

		/*
		 * Get the join attribute value of the tuple
		 */
		keyval = ExecEvalExpr(keyexpr, econtext, &isNull, NULL);

		/*
		 * Compute the hash function
		 */
		if (!isNull)			/* treat nulls as having hash key 0 */
		{
			uint32		hkey;

			hkey = DatumGetUInt32(FunctionCall1(&hashtable->hashfunctions[i],
												keyval));
			hashkey ^= hkey;
		}

		i++;
	}

	MemoryContextSwitchTo(oldContext);

	return hashkey;
}

/*
 * ExecHashGetBucketAndBatch
 *		Determine the bucket number and batch number for a hash value
 *
 * Note: on-the-fly increases of nbatch must not change the bucket number
 * for a given hash code (since we don't move tuples to different hash
 * chains), and must only cause the batch number to remain the same or
 * increase.  Our algorithm is
 *		bucketno = hashvalue MOD nbuckets
 *		batchno = (hashvalue DIV nbuckets) MOD nbatch
 * where nbuckets should preferably be prime so that all bits of the
 * hash value can affect both bucketno and batchno.
 * nbuckets doesn't change over the course of the join.
 *
 * nbatch is always a power of 2; we increase it only by doubling it.  This
 * effectively adds one more bit to the top of the batchno.
 */

void
ExecHashGetBucketAndBatch(HashJoinTable hashtable,
						  uint32 hashvalue,
						  int *bucketno,
						  int *batchno)
{
	uint32		nbuckets = (uint32) hashtable->nbuckets;

	/* CSI3130: multiple batches disabled – there is always exactly one batch. */
	*bucketno = hashvalue % nbuckets;
	*batchno  = 0;
}


/*
 * ExecScanHashBucket
 *		scan a hash bucket for matches to the current outer tuple
 *
 * The current outer tuple must be stored in econtext->ecxt_outertuple.
 */
HeapTuple
ExecScanHashBucket(HashJoinState *hjstate,
				   ExprContext *econtext)
{
	List	   *hjclauses = hjstate->hashclauses;
	HashJoinTable hashtable = hjstate->hj_HashTable;
	HashJoinTuple hashTuple = hjstate->hj_CurTuple;
	uint32		hashvalue = hjstate->hj_CurHashValue;

	/*
	 * hj_CurTuple is NULL to start scanning a new bucket, or the address of
	 * the last tuple returned from the current bucket.
	 */
	if (hashTuple == NULL)
		hashTuple = hashtable->buckets[hjstate->hj_CurBucketNo];
	else
		hashTuple = hashTuple->next;

	while (hashTuple != NULL)
	{
		if (hashTuple->hashvalue == hashvalue)
		{
			HeapTuple	heapTuple = &hashTuple->htup;
			TupleTableSlot *inntuple;

			/* insert hashtable's tuple into exec slot so ExecQual sees it */
			inntuple = ExecStoreTuple(heapTuple,
									  hjstate->hj_HashTupleSlot,
									  InvalidBuffer,
									  false);	/* do not pfree */
			econtext->ecxt_innertuple = inntuple;

			/* reset temp memory each time to avoid leaks from qual expr */
			ResetExprContext(econtext);

			if (ExecQual(hjclauses, econtext, false))
			{
				hjstate->hj_CurTuple = hashTuple;
				return heapTuple;
			}
		}

		hashTuple = hashTuple->next;
	}

	/*
	 * no match
	 */
	return NULL;
}

/*
 * ExecHashTableReset
 *
 *		reset hash table header for new batch
 */
void
ExecHashTableReset(HashJoinTable hashtable)
{
	MemoryContext oldcxt;
	int			nbuckets = hashtable->nbuckets;

	/*
	 * Release all the hash buckets and tuples acquired in the prior pass, and
	 * reinitialize the context for a new pass.
	 */
	MemoryContextReset(hashtable->batchCxt);
	oldcxt = MemoryContextSwitchTo(hashtable->batchCxt);

	/* Reallocate and reinitialize the hash bucket headers. */
	hashtable->buckets = (HashJoinTuple *)
		palloc0(nbuckets * sizeof(HashJoinTuple));

	hashtable->spaceUsed = 0;

	MemoryContextSwitchTo(oldcxt);
}

void
ExecReScanHash(HashState *node, ExprContext *exprCtxt)
{
	/*
	 * if chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.
	 */
	if (((PlanState *) node)->lefttree->chgParam == NULL)
		ExecReScan(((PlanState *) node)->lefttree, exprCtxt);
}
