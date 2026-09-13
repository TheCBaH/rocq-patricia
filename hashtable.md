# Persistent hash-table feasibility investigation

This note records the original feasibility investigation for a functional
hash table. The selected contract is now in [hashtable-design.md](hashtable-design.md),
with an [implementation plan](hashtable-plan.md) and [tracker](hashtable-todo.md).
The design also compares HAMT and CHAMP runtime and Rocq proof costs. These
documents plan a new module; they do not claim an implemented or proved hash
table and do not change the existing Patricia plan.

## Relationship to the existing maps

The existing positive-key and direct-string Patricia maps are already
persistent: an update rebuilds only its affected path and may retain untouched
subtrees.  They route from key bits directly, which gives deterministic
structure and supports the current critical-prefix merge and union algorithms.

A hash table would be a different map representation.  It routes from a hash
of the key, must retain and compare original keys to resolve collisions, and
has different performance and proof tradeoffs.  It should be introduced as a
new module rather than as an optimization or backend replacement for either
Patricia map.

## Preferred design for string lookup and update

For the target workload—persistent lookup and point update over strings, with
no merge or ordered traversal requirement—the preferred design is a 32-way
bitmap HAMT.  “32-way” means that one node consumes a five-bit hash chunk and
therefore has `2^5 = 32` logical slots; it does not mean that hashes are
32-bit.  A CHAMP-style layout is a suitable optimized native variant: it keeps
data entries and child nodes in separate compact regions, reducing node visits
and improving locality.  The initial proved source model should use the
simpler bitmap-HAMT layout below; it has the same observable map semantics.

A hash-PATRICIA table built from the existing positive-integer map is a good
prototype and proof baseline, but not the preferred final layout.  It takes
roughly `log2 n` binary routing steps for `n` distinct hashes, while a 32-way
HAMT takes roughly `log32 n` levels.  The Patricia version gains little from
critical-prefix structure when its keys are random-looking hashes.

This recommendation is workload-dependent.  A HAMT must hash every query
string before routing.  The existing direct string Patricia map can be better
for long or prefix-related strings because it may inspect only discriminating
bytes before the final exact-key comparison.  Benchmark both designs before
replacing an existing map.

## HAMT and CHAMP

**HAMT** means *hash-array mapped trie*.  It treats the hash as a sequence of
small chunks rather than as one comparison key.  With five-bit chunks, each
node has up to 32 logical slots.  A bitmap records which slots exist, and a
compact child array contains only those slots.  Thus a sparse node does not
allocate an always-mostly-empty 32-entry array.  To follow hash slot `s`, test
bit `s` in the bitmap and use the population count of earlier set bits as the
compact-array index.  A full-hash collision is handled by a small collection
of full keys, checked with key equality.

For example, if a node's bitmap has slots 1, 7, and 20 set, its compact child
array has three entries.  Hash slot 7 has compact index 1 because exactly one
set bit precedes it.  Lookup is therefore a bitmap test, a population count,
and one array access per level.

**CHAMP** means *compressed hash-array mapped prefix-tree*.  It is a HAMT
layout specialized for persistent maps.  Instead of treating every occupied
slot as a child-node pointer, it maintains two bitmaps:

- a data bitmap, whose compact array entries hold direct `(key, value)` pairs;
- a node bitmap, whose compact array entries hold child nodes.

A shallow entry can therefore live directly in its parent node.  Only slots
where several hashes share the current chunk need a child node.  This reduces
indirection, object count, and array traffic for common lookup/update paths.
The two bitmap populations determine the offsets of the data and node regions;
the regions may be stored as separate immutable arrays or as one compact array
with a fixed layout.

Both structures have the same abstract semantics and use the same hash chunk,
collision, and persistence rules.  CHAMP is an implementation optimization of
the simple bitmap-HAMT proof model, not a different public map contract.  The
recommended proof order is consequently: prove the one-bitmap HAMT first,
then prove that each CHAMP operation refines its lookup semantics and preserves
the corresponding compact-layout invariants.

## Candidate representation

The natural persistent design is a hash-array mapped trie (HAMT): immutable
nodes consume fixed-width chunks of a key hash, use a bitmap to compact sparse
child arrays, and copy only the path modified by an operation.  A leaf stores
the full key, its value, and optionally a cached hash.  Equal full hashes that
contain distinct keys use a collision bucket checked with key equality.

Typical operations are expected constant time under a suitable hash
distribution, while retaining the usual persistent properties:

- `set` and `remove` allocate a changed root-to-leaf path only;
- lookup and an unchanged update return an existing subtree where possible;
- old versions remain usable without copying the complete table; and
- collisions remain semantically safe because all candidates are compared as
  full keys.

The worst case is still linear in the collision-bucket size.  Expected-time
claims therefore require a workload or hash-distribution assumption; they are
not functional-correctness theorems.

## Implementation design

For the initial string map, use `Hashtbl.seeded_hash seed key` and consume five
bits at a time.  It returns a nonnegative OCaml `int` and has the required
equality-congruence property.  The seed belongs to the persistent table and
must be retained unchanged by every derived version.  This makes collision
attacks harder without changing a table's routing after an update.

Although a 64-bit OCaml `int` has a 62-bit nonnegative range, the configured
OCaml 4.14 runtime deliberately folds `Hashtbl.hash` and `seeded_hash` to the
30-bit range `0 .. 2^30 - 1` for 32/64-bit compatibility.  It therefore uses
exactly six five-bit HAMT levels.  Converting that `int` result to `Int64`
does not create additional hash bits and should not be done.

Use `Int64` only if profiling demonstrates that a custom 64-bit string hash is
needed.  That is a distinct hash contract and native-refinement obligation,
not an improvement obtained from the standard hash.  A true 64-bit hash would
use at most thirteen levels.  The proof model should state the selected bounded
word type explicitly; native hashing and word primitives remain behind the
same explicit refinement boundary as other optimized operations.

At a level `shift`, the hash slot and its compact-array location are:

```text
slot h shift = (h >> shift) & 31
bit  h shift = 1 << slot h shift
index bitmap b = popcount (bitmap & (b - 1))
```

The bitmap says which of the 32 slots are populated.  Its children are stored
densely in increasing slot order, so `index bitmap (bit h shift)` identifies
the child without allocating a 32-entry array.  A suitable source-level shape
is:

```text
tree :=
  | Empty
  | Leaf      of hash * key * value
  | Collision of hash * (key * value) list
  | Branch    of bitmap * tree list
```

`get tree shift key hash` first derives the slot.  It follows the matching
child of a branch; it checks the stored full key in a leaf; and it linearly
searches a collision bucket with `equal`.  The supplied `shift` increases by
five at each branch.  A collision bucket is reached only after all hash chunks
have been consumed, or immediately when two different keys have equal full
hashes.

`set` is purely functional.  It returns the old node when the key/value pair
is observably unchanged; otherwise it returns a new leaf, bucket, or branch
whose dense child list is copied only at the changed index.  Its key cases are:

1. In `Empty`, return a leaf.
2. In a `Leaf` with an equal key, replace the value only when it changed.
3. In a `Leaf` with a different key and equal full hash, create a collision
   bucket.
4. In two different hashes, make a branch at the first five-bit chunk where
   they differ.  If this level's slots agree, recurse at `shift + 5` until
   they diverge.
5. In a `Branch`, insert or replace the selected child and rebuild the
   bitmap/list pair only if that child changed.

`remove` follows the same route.  Removing the last collision-bucket entry
returns `Empty`; a two-entry bucket becomes a `Leaf`; and a branch with no
remaining children becomes `Empty`.  The initial verified implementation
should retain a branch that has one child: this keeps the implicit
shift-by-depth interpretation simple and is bounded by the hash width.  A
more compact representation may later add an explicit skip/prefix node, but
that is an optimization with its own routing proof.

## Representation invariants

For every `Branch bitmap children`, the number of children must equal
`popcount bitmap`, child order must agree with increasing set bits, and no
child may be `Empty`.  At a recursive call with `shift`, every descendant hash
must agree with the branch path on all earlier five-bit chunks.  Leaves retain
their actual hash, and all keys in a collision bucket have that same hash and
are pairwise unequal.

These invariants give both lookup routing and finite-map uniqueness.  They
also make native arrays an implementation detail: the initial Rocq model can
use a list with an indexed replacement lemma, while extracted OCaml can refine
that operation to copying a compact array slice.

## API and proof boundary

A generic implementation needs an abstract key contract with decidable
equality and a hash that respects it:

```text
equal k1 k2 = true  ->  hash k1 = hash k2
```

Rocq proofs should establish map semantics from that contract, including
collision-bucket uniqueness, routing from each hash chunk, bitmap rank/index
correctness, insertion/removal collapse, and persistence of unchanged
subtrees.  They must not assume that unequal keys have unequal hashes.

As with the current native extractors, any OCaml hash primitive, finite-width
integer representation, array operation, or custom optimized realizer needs
either a refinement theorem or explicit inclusion in the trusted boundary.
Adversarial-input resilience and randomized/hash-seeded behavior are separate
security and reproducibility decisions.

## Correctness plan

The functional-correctness claim should be staged, with the simple immutable
bitmap-HAMT as the proved reference implementation.

1. Define the key interface in Rocq: a type of keys, equality reflecting key
   equality, a bounded hash word, and the hash-congruence law.  Do not require
   unequal keys to have different hashes.
2. Specify list collision buckets and prove `find`, replacement, and removal
   correct, preserving the no-duplicate-key invariant.
3. Prove the bitmap primitives: slot bounds, one-bit masks, `popcount` rank,
   and correspondence between a set bitmap bit and the indexed dense child.
   Prove insertion and removal from the child list preserve this
   correspondence.
4. Define a well-formedness predicate indexed by hash depth.  It records the
   bitmap/list invariant, the hash chunks selected by every branch, the hash
   stored in each leaf, and collision-bucket key uniqueness.
5. Prove `get_correct_wf`: lookup returns `Some v` exactly when the abstract
   finite map binds the queried key to `v`.
6. Prove `set_correct_wf` and `remove_correct_wf` simultaneously with
   well-formedness preservation.  The theorems state the usual pointwise
   update/removal laws; optional native identity reuse is an optimization, not
   part of this semantic claim.
7. Derive finite-map extensionality, `mem`, `elements` soundness/completeness,
   and persistence: old trees retain their lookup semantics after a new tree
   is returned.
8. Extract the reference model first.  Only then refine list replacement to
   immutable compact arrays and, if desired, the bitmap node to CHAMP's
   separate data/node maps.  Each native string-hash, word, bitmap, and array
   primitive needs a stated refinement contract.

The height bound `ceil(hash_width / 5)` is a structural theorem.  Expected
constant-time and collision-resistance claims are not: they additionally
depend on the hash function and workload.  For untrusted keys, use a stable
per-table randomized seed (retained by all derived versions) or document that
collision attacks are outside the threat model.

## Evaluation criteria

Benchmarking a persistent table against mutable `Stdlib.Hashtbl` must account
for persistence.  In particular, retain old versions or copy the mutable table
for each update, and measure allocation, retained heap, lookup, update,
remove, and collision-heavy inputs.  The existing Patricia benchmarks may
continue to use `Stdlib.Hashtbl` as a mutable performance reference, but they
do not establish a persistent hash-table comparison.

Before work begins, select the string-hash contract, collision policy,
branching width, and seed policy.  Those choices define a new specification
and proof plan rather than extending `patricia-todo.md`.
