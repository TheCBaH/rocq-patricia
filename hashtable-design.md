# Persistent generic hash table: design

Date: 2026-09-13. Status: H0 complete; source/reference implementation and
initial proofs in progress. The tracker is authoritative for delivery gates.

This document turns the investigation in [hashtable.md](hashtable.md) into an
implementation contract. The [plan](hashtable-plan.md) defines delivery gates;
[the tracker](hashtable-todo.md) owns task status and evidence. The reference
is this directory's `Patricia.v` / `StringPatricia.v` development, its separate
proof files, extractors, abstract OCaml wrappers and differential tests.
The existing Patricia public specification continues to describe only Patricia.

## Scope and decisions

Deliver a new persistent map for any key type supplying lawful equality and
hashing. Values are polymorphic. Strings, integers and structured records are
example instances, not restrictions on the core or public API. Prove the
functional bitmap HAMT in Rocq and extract its algorithm to OCaml. Deliver
ordinary list-based extraction first; then a compact-array backend with explicit
refinement contracts. Neither backend replaces either Patricia map.

| Decision | Selected contract |
| --- | --- |
| Routing | One bitmap per branch, 32 slots, five hash bits per level, least significant chunk first |
| Hash | A total, deterministic function of immutable seed and key, returning a 30-bit word |
| Public key interface | OCaml functor parameter with `type t`, `equal` and seeded `hash` |
| Hash adaptation | Normalize the supplied OCaml `int` to its low 30 bits before routing |
| String example | `String.equal` and `Stdlib.Hashtbl.seeded_hash`; other instances supply their own functions |
| Seed | Explicit OCaml `int` at construction; retained by every derived map; no hidden random state |
| Collision policy | Full-key equality, unique-key list bucket for equal full hashes |
| Deletion | Remove empty children; retain unary branches; bucket of size one becomes a leaf |
| Value comparison | None required; `set` replaces the value even if the old value appears equal |
| Traversal | Unspecified public order; each binding exactly once |
| First native platform | 64-bit OCaml, matching the existing default 4.14.3 toolchain |
| Deferred | CHAMP, skip nodes, custom 64-bit hash, merge/union, ordered traversal, `Map.S` compatibility |

Explicit seeds permit reproducible runs. Callers can supply randomly generated
seeds for separate tables, but this API makes no collision-resistance or security
guarantee. Hashing must remain stable during a table's lifetime; portable
serialization across runtime/hash versions is outside this API.

The wrapper normalizes every supplied hash with `h land 0x3fffffff`, including
negative results. In the Rocq adapter model use integer modulo `2^30`, prove
its bound and congruence, and prove agreement with the native mask. Thus six
chunks cover the selected routing domain for every key instance. The local
OCaml 4.14.3 `runtime/hash.c` already applies that mask for the string example. The branch bitmap is a
*different* 32-bit quantity: slot 31 requires `1 << 31` and a full bitmap is
`2^32 - 1`. Both fit a nonnegative 63-bit OCaml integer on the selected
platform. A future 32-bit port needs another bitmap representation and proofs.

## HAMT versus CHAMP: runtime and proof cost

Recommendation: use the one-bitmap HAMT for the first verified OCaml release.
CHAMP is a promising later native layout, not a demonstrated winner for this
repository's lookup/update workload. CHAMP is itself a HAMT variant; the
comparison here is specifically with the simple child-only layout above.

The original CHAMP paper reports better memory footprint, iteration and equality
performance on the JVM while maintaining competitive lookup/insertion/deletion.
Those results establish motivation, not OCaml performance predictions. See
[Steindorfer and Vinju, OOPSLA 2015, sections 3–6](https://ir.cwi.nl/pub/24029/24029B.pdf).
The following proof-cost assessment is an engineering inference from the two
representations, not a measured Rocq development result.

| Criterion | One-bitmap HAMT | CHAMP |
| --- | --- | --- |
| Lookup | One occupancy/rank path, then a leaf or bucket | Inline data can avoid a leaf visit; distinguishes data and child occupancy |
| Persistent point updates | One child region to copy; straightforward leaf/bucket cases | Can reduce leaf objects, but data-to-child promotion and reverse migration add work |
| Memory and iteration | Separate leaves add objects/indirection | Grouped data can improve locality; benefit depends on actual OCaml storage |
| Full-hash collisions | Linear bucket search | Same worst case with the same bucket policy |
| Basic invariants | One bitmap/popcount correspondence | Two correspondences plus disjoint data/node bitmaps |
| Insertion proof | Child replacement/insertion and join | Also move an inline binding into a child while preserving both region ranks |
| Removal proof | Remove empty child; retain unary branch | Also prove singleton child inlining and its routing/normalization conditions |
| Native refinement | One child sequence representation | Data and child regions, offsets, migrations and potentially heterogeneous storage |
| Initial proof effort | Lower | Higher, although much of hash/bucket/rank theory is reusable |

Both consume at most six routing chunks in this design. CHAMP does not improve
that bound or solve poor hash distribution. The likely advantage is in object
count, memory traffic and locality, rather than a different asymptotic lookup
bound. Long-key hashing and collision equality can dominate either layout.

A typed OCaml representation with separate `(key * value) array` and child
arrays is easier to relate to Rocq than a heterogeneous packed array. However,
pair allocations and separate array headers may reduce CHAMP's intended memory
savings. An untyped packed array using `Obj` would enlarge the trusted boundary;
it is not an acceptable default merely to imitate a JVM implementation.
Inspect and measure the actual extracted storage before making a speed claim.

Full canonical CHAMP normalization is unnecessary for pointwise map correctness.
A two-bitmap variant retaining unary branches can reduce proof work, but must
not inherit claims about canonical structure or fast structural equality from
the paper. In particular, a singleton binding can be inlined into a parent;
a unary internal branch containing multiple bindings cannot simply be promoted
when depth is implicit. Collision entry order also needs attention before any
claim of canonical representation.

The staged choice trades a usable early release against the cost of maintaining
two verified representations if CHAMP is later added. If measurements establish
that CHAMP is required, reuse the hash, bucket and bitmap lemmas and prove its
operations directly against abstract bindings or through a HAMT representation
relation. Do not require a structural conversion to run on every operation.
A refinement must handle inlined entries at their original slot/depth, not just
replace each parent-level inline binding with an unpositioned leaf.

Revisit the choice after the compact-array HAMT baseline: compare equivalent
OCaml layouts with identical hashes, seeds, collision policy and workloads.
A list HAMT versus an array CHAMP would confound container and layout effects.
Prefer CHAMP only when measured memory/runtime gains justify the extra migration,
normalization and representation proofs. Keep it outside the current release
until that decision has evidence.

## Abstract contract and public API

The generic Rocq development takes `K : Type`, `E : K -> K -> Prop`,
`eqb : K -> K -> bool`, `Seed : Type`, and normalized
`hash : Seed -> K -> N`, with explicit hypotheses:

```text
Equivalence E                         (* reflexive, symmetric, transitive *)
eqb k q = true <-> E k q
hash seed k < 2^30
E k q -> hash seed k = hash seed q
```

Maps are over key equivalence classes: `E` need not be Rocq propositional
equality. This supports case-insensitive strings or records compared by an ID.
Ordinary equality is a simple instance. Hash congruence is a substantive proof
obligation for custom equivalences; unequal keys may always share a hash. No
injectivity, distribution, ordering or value equality assumption is permitted.
Pass contracts as section parameters or theorem hypotheses, not global axioms.
Prove equivalence/reflection and hash congruence for supplied Rocq instances.
For user-written OCaml instances these laws are documented obligations, not
properties that the functor type system can check.

Both callbacks must be total, deterministic and observationally pure. Keys
must retain the equality/hash-relevant state they had when stored, for as long
as any persistent version retains them. Mutable fields irrelevant to both
callbacks are allowed. Closure state affecting a callback must also stay stable.
Normalization ensures bounds, but cannot repair inconsistent equality/hashing.

Proposed `HashMap.mli` (operation names and argument order follow Patricia):

```ocaml
module type KEY = sig
  type t
  val equal : t -> t -> bool
  val hash : seed:int -> t -> int
end

module Make (Key : KEY) : sig
  type key = Key.t
  type 'a t
  val empty : seed:int -> 'a t
  val singleton : seed:int -> key -> 'a -> 'a t
  val is_empty : 'a t -> bool
  val get : key -> 'a t -> 'a option
  val mem : key -> 'a t -> bool
  val set : key -> 'a -> 'a t -> 'a t
  val remove : key -> 'a t -> 'a t
  val of_list : seed:int -> (key * 'a) list -> 'a t
  val elements : 'a t -> (key * 'a) list
end
```

A string instance is just an application of the same public functor:

```ocaml
module StringHashMap = HashMap.Make (struct
  type t = string
  let equal = String.equal
  let hash ~seed key = Hashtbl.seeded_hash seed key
end)
```

An integer instance uses the full native `int` key domain, including zero and
negative keys (unlike the positive-key Patricia wrapper):

```ocaml
module IntHashMap = HashMap.Make (struct
  type t = int
  let equal (x : int) (y : int) = x = y
  let hash ~seed key = Hashtbl.seeded_hash seed key
end)

let numbers = IntHashMap.empty ~seed:0
let numbers = IntHashMap.set (-7) "negative" numbers
let numbers = IntHashMap.set 0 "zero" numbers
let found = IntHashMap.get (-7) numbers  (* Some "negative" *)
```

Model integer keys with Rocq `Z`; relate the native instance to the OCaml
`min_int .. max_int` domain. Only hashes are normalized to 30 bits, never keys:
different full integers that share a normalized hash remain distinct bindings.
Include `min_int`, `max_int`, zero and negative integers in the instance tests.
These examples describe the planned API; its implementation is still open.

An unseeded hash is also usable as `let hash ~seed:_ key = user_hash key`;
this forfeits seed-dependent routing, not functional correctness. No ordering,
serialization to strings or polymorphic equality is required of keys.

`of_list` uses first occurrence wins, matching `StringPatriciaMap`. A table
contains its seed and root. Its key operations are fixed by the functor instance;
clients cannot substitute callbacks or precomputed hashes on individual map
operations. Constructors, depth, fuel, normalized hashes and arrays stay private.
Constant and controlled hashes are ordinary lawful public functor instances.
The API hides malformed trees; semantic guarantees also require lawful callbacks.

`set` on an equivalent key retains the already stored key representative and
replaces its value. `of_list` must preserve both the first representative and
first value in each equivalence class; implement a first-to-last insert-if-absent
fold, rather than blindly reusing a right-fold setter. `elements` returns these
stored representatives, not every equivalent spelling of a key.

For valid `m`, all keys `k`, `q`, and values `v`, prove:

```text
get q (empty seed) = None
get q (set k v m) = if eqb q k then Some v else get q m
get q (remove k m) = if eqb q k then None else get q m
mem k m = true <-> exists v, get k m = Some v
(exists r, In (r,v) (elements m) /\ E k r) <-> get k m = Some v
NoDupA E (map fst (elements m))
E k q -> get k m = get q m
is_empty m = true <-> forall k, get k m = None
```

Also prove validity and seed preservation for every constructor/update,
singleton and bulk-load laws, and extensional map equivalence defined by
pointwise lookup. Do not claim equal tree shapes, equal traversal order across
seeds, or Rocq record equality from equivalent bindings.

Persistence means old roots keep their bindings after later updates. In Rocq
this follows from purity and the lookup laws. In OCaml it additionally depends
on immutable node storage. Values themselves may contain mutable references;
the map does not snapshot or deep-copy payloads. Physical root reuse and exact
allocation counts are separate optimization claims, not these theorems.

## Source representation and invariant

Use logical `N` arithmetic for hashes and bitmaps and lists for dense children:

```text
tree A := Empty
        | Leaf (h : N) (k : K) (v : A)
        | Collision (h : N) (entries : list (K * A))
        | Branch (bitmap : N) (children : list (tree A))
table A := { seed : Seed; root : tree A }
slot h d = (h >> (5*d)) & 31
rank bitmap s = popcount (bitmap & ((1 << s) - 1))
```

Define independent `bindings` by flattening all leaves and buckets, without
routing through `get`. Use it to specify membership and uniqueness so lookup
correctness is not circular.

`wf seed d prefix t` records the consumed slot list `prefix`, of length `d`:

- `0 <= d <= 6`; every stored hash is bounded and equals `hash seed key`.
- Each stored hash has the chunks in `prefix` at depths below `d`.
- Leaf has one binding. Collision has at least two entries with pairwise non-equivalent keys
  and one common full hash; collision nodes may occur before depth six.
- Branch requires `d < 6`, `bitmap < 2^32`, a nonzero bitmap, and
  `length children = popcount bitmap`. Its children are nonempty and ordered
  by increasing occupied slot. A child at slot `s` satisfies
  `wf seed (d+1) (prefix ++ [s])`.
- Bindings have no duplicate keys modulo `E`. Prove this compositionally using disjoint
  branch slots plus hash congruence and bucket uniqueness.

The root invariant is `wf seed 0 [] root`. Empty is valid at any permitted
depth, but never stored as a branch child. At depth six only empty, leaf or
collision forms are valid. Prove at most six branch nodes occur on a path;
this does not bound collision-bucket size.

## Algorithms and termination

`get` hashes the query once at the table boundary, then structurally descends.
A leaf checks the full key using the supplied equality; a bucket searches by full-key equality; a branch
tests the query slot bit and uses its rank to select the dense child.

`set` replaces an equal key in a leaf or bucket. Distinct keys with equal
hashes share a bucket. Distinct hashes use `join d left right`: compare the
current chunks, form two ordered children if they differ, otherwise create a
unary branch around `join (d+1) left right`. Do not jump directly to a deeper
branch without recording all preceding equal chunks. Joining an existing
collision node with a different hash uses the same procedure.

At a branch, insert a leaf at rank if the bit is absent, or recursively replace
the existing child. Bucket replacement preserves uniqueness. Updating an equivalent key retains its stored key and always stores the supplied value; polymorphic structural equality must not
be used on payloads (which may be functions or cyclic objects).

`remove` returns unchanged structure on a miss where convenient. It deletes the
matching bucket entry, normalizes bucket size zero/one, and removes a branch's
bit and dense entry if a recursive result is empty. An empty branch becomes
empty; a unary branch stays a branch, since promoting its child would change
the depth interpretation.

Use explicit bounded recursion on remaining levels for `set` and `join`, with
initial budget six, and structural recursion for buckets. Specify total raw
workers, including an unreachable exhausted-budget branch, and prove that valid
calls never take an invalid fallback. At depth six valid insertions can only
replace a key or extend an equal-hash bucket. The supporting separation lemma
says two different bounded hashes disagree in one of the six chunks. Fuel is
internal; removing its runtime overhead is optional after the reference gate.

## Proof decomposition

| Layer | Required results |
| --- | --- |
| Hash chunks | Slot bounds; six-chunk reconstruction/separation; equal-key route agreement |
| Bitmap and dense lists | Rank bounds for present/absent slots; bit/rank bijection; full 32-slot boundary; indexed insert/replace/delete correspondence |
| Buckets | Lookup, replacement and deletion laws; unique keys; common hash; normalization preserves bindings |
| Routing and join | Prefix extension; disjoint slot bindings; join termination, validity and binding union for different hashes |
| Map operations | Independent binding specification; lookup correctness; update/removal equations and invariant preservation |
| Derived API | Membership, emptiness, singleton, first-wins bulk load, enumeration, extensional equivalence and seed preservation |
| Structure | Six-branch height bound; retained unary branches respect depth |

Give every public theorem a stable name and include it in the assumption audit.
The target is kernel-checked proofs without `Admitted` or global hash axioms;
contract hypotheses remain explicit in generic theorem statements.

## Extraction and compact-array refinement

Follow [PatriciaReferenceExtract.v](PatriciaReferenceExtract.v) for a separately
named executable reference, and [PatriciaExtract.v](PatriciaExtract.v) for
explicit extraction bindings. Do not override entire `get`, `set`, `remove`
or `join` algorithms with handwritten OCaml strings.

The reference keeps executable Rocq lists, arithmetic and control flow. Supply
key equality and hash callbacks once through `HashMap.Make`; differential tests
feed the same key instance and normalization to both backends. Keep the source
core generic through extraction; do not specialize it permanently to strings. A fully executable pure test instance
also uses a simple bounded Rocq-defined hash, proving the abstract contract
without an OCaml hash axiom. Agreement using a shared native hash does not
independently validate that hash's foreign contract.

Avoid globally mapping unbounded `N` to `int` without bounding intermediate
operations. The reference may retain structural numerals; optimized primitives
need proved ranges for hashes, bitmaps, rank, masks and shifts, including slot
31 and the full bitmap. Use a bounded popcount worker with source-defined
control flow, then extract its scalar operations under those bounds.

For native children, introduce an abstract persistent sequence interface with
`length`, guarded `get`, `insert`, `replace` and `delete`. First instantiate it
with lists. Prove map workers against its sequence-view equations, then model
arrays and prove the same equations. Do not globally extract Rocq lists as
arrays: bucket lists and recursive pattern matches have different requirements.
Rocq's positivity/termination requirements for recursive trees under an abstract
container must be resolved in an early prototype; a separate native node model
with a relation to source trees is an acceptable implementation route.

The actual OCaml array realizers must allocate a fresh destination for updates,
copy unaffected ranges, and write only before publication. Array references
never escape the abstract API. State a relation `R seed source native` covering
seed equality, scalar representations, child sequence views and recursive
nodes; prove each modeled operation preserves `R` and agrees with lookup.
A pure array model does not prove actual OCaml heap immutability: actual copy,
bounds, access and no-mutation behavior remain foreign obligations unless a
separate target heap proof discharges them.

Maintain a primitive inventory with source symbol, OCaml realizer, precondition,
refinement theorem and remaining trust. It covers each key instance's equality,
key representation and seeded hashing, hash normalization, native word operations, array operations, standard extraction,
OCaml compilation and runtime behavior. Audit extraction directives and generated
workers. Runtime differential tests support this boundary; they do not replace
Rocq proofs or establish end-to-end verified compilation.

## Evaluation and acceptance

Correctness gates require proofs, assumption audits, both extractions, abstract
wrapper compilation, invariant checks and differential operation histories
against an association-list oracle using the supplied equality (and, for
instances with a compatible comparator, `Map.Make`). Include constant-hash collisions, all six divergence
levels, slots 0/31, full branches, deletion normalization, re-insertion, duplicate
bulk inputs, integers, tuples/records, arbitrary byte strings, custom key
equivalences, negative/large raw hash results, multiple seeds and retained roots.
Use function and reference payloads in targeted tests without polymorphic
comparison. Recheck retained roots after later updates to detect array mutation.

Benchmark the list reference, native HAMT and comparator-compatible `Map.Make`
instances on identical checked workloads for integer, string and structured keys.
Include direct-string Patricia and `Map.Make(String)` in the string subset. Label mutable `Hashtbl`
separately; a persistence comparison must copy it for each retained version.
Measure lookup/update/remove, allocation and retained heap across short, long,
prefix-related and collision-heavy keys. Record seed, runtime/compiler, input
size and version-retention policy. No expected-time theorem or empirical
speedup is a release prerequisite; publish measured results without assuming
that the HAMT wins. Supplied key hashing and equality costs are part of the workload.
