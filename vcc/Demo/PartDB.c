#include <vcc.h>
#include "Spec.h"
#include <stdlib.h>

#define MAXPART 64
#define ISSET(n, v) (((v) & (1ULL << (n))) != 0)

typedef int bool;

typedef _(claimable) struct _Partition {
  bool active;

  struct _PartitionDB *db;
  unsigned idx;
  _(invariant idx < MAXPART && db->partitions[idx] == \this)

  _(ghost volatile bool signaled)
  _(invariant signaled <==> ISSET(idx, db->allSignaled))
  _(invariant signaled ==> active)

  _(ghost \claim db_claim)
  _(invariant \mine(db_claim) && \claims_object(db_claim, db))
} Partition;

typedef Partition *PPartition;

_InterlockedCompareExchange(PPartition)

typedef _(claimable) struct _PartitionDB {
  volatile uint64_t allSignaled;
  volatile PPartition partitions[MAXPART];
  _(invariant \forall unsigned i; i < MAXPART ==> partitions[i] == \old(partitions[i]) ||
                   \old(partitions[i]) == NULL || !\old(partitions[i])->\closed)
  _(invariant \forall unsigned i; i < MAXPART ==> ISSET(i, allSignaled) == \old(ISSET(i, allSignaled)) ||
                   \inv2(partitions[i]))
} PartitionDB;

void part_send_signal(Partition *part _(ghost \claim c))
  _(requires \wrapped(c) && \claims(c, part->\closed))
{
  PartitionDB *db = part->db;
  uint64_t idx = part->idx;

  if (!part->active) return;

  _(assert {:bv} \forall int i, j; uint64_t v; 0 <= i && i < 64 && 0 <= j && j < 64 ==>
    i != j ==> (ISSET(j, v) <==> ISSET(j, v | (1ULL << i))))

  _(atomic part, db, c) {
    _(ghost part->signaled = \true)
    InterlockedBitSet(&db->allSignaled, idx);
  }
}

// removal of partition requires only ownership of the partition
// nothing is said about the database
void remove_from_db(Partition *part)
  _(requires \wrapped0(part))
  _(ensures \mutable(part))
  _(writes part)
{
  PartitionDB *db = part->db;
  uint64_t idx = part->idx;

  _(atomic db) {
    _(unwrap part)
    // TODO we should allow begin_update() to take additional claims
   _(assert \active_claim(part->db_claim))
    _(begin_update)
    db->partitions[idx] = NULL;
  }
}

uint64_t add_to_db(PartitionDB *db, Partition *part _(ghost \claim c))
  _(requires part->active)
  _(always c, db->\closed)
  _(maintains \wrapped(db))
  _(writes \extent(part), db)
  _(ensures \result == MAXPART ==> \mutable(part))
  _(ensures \result < MAXPART ==> \wrapped(part) && part->idx == \result && part->db == db)
{
  unsigned i;
  Partition *old_value;

  // this loop is only an optimization from VCC point of view
  // we just locate i which is likely to be NULL a few lines down from here
  for (i = 0; i < MAXPART; ++i)
    _(writes {})
  {
    _(atomic db, c) {
      old_value = db->partitions[i];
    }
    if (old_value == NULL)
      break;
  }

  if (i < MAXPART) {
    part->db = db;
    part->idx = i;
    _(ghost part->db_claim = \make_claim({db}, \true))
    _(atomic db, c) {
      old_value = InterlockedCompareExchange(&db->partitions[i], part, NULL);
      _(ghost part->signaled = ISSET(i, db->allSignaled))
    }
    // if the entry was still NULL, we could stick our partition in there
    // and can now wrap it
    if (old_value == NULL) {
      part->active = 1;
      _(wrap part)
      return i;
    }
  }

  return MAXPART;
}

/*`
Verification of _Partition#adm succeeded.
Verification of _PartitionDB#adm succeeded.
Verification of part_send_signal succeeded.
Verification of remove_from_db succeeded.
Verification of add_to_db succeeded.
Verification of part_send_signal#bv_lemma#0 succeeded.
`*/
