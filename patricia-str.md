# Direct-string Patricia map performance analysis

Last reviewed: 2026-08-30

## Scope and conclusion

This note records the performance analysis and design rationale for the direct
byte-string map in `StringPatricia.v`, using the implementation, extraction
directives, proof invariants, and measurements recorded in
[`patricia-bench.md`](patricia-bench.md). Current and proposed work is tracked
only in [`patricia-todo.md`](patricia-todo.md).

The string map already routed at bit granularity. The original question was
how to implement its critical-bit operations without paying repeated division,
remainder, bounds-check, and whole-prefix-scan costs.

There were two distinct performance problems in the original extracted
implementation:

1. **Biased union had the wrong execution path.** `union_left` and
   `union_right` went through generic fuelled `combine`. That computed the size
   of both inputs and rebuilt one-sided subtrees, causing the dominant
   disjoint-union gap.
2. **Ordinary string mutations did more string and tree work than necessary.**
   Routing decoded a logical bit position with `/ 9` and `mod 9` at every
   branch; `first_diff` scanned one logical bit at a time; and `set` first
   routed to a leaf and then traversed the tree again to update or insert.

The following sequence was completed in the native extraction:

1. implement specialized, structurally sharing biased unions;
2. replace bit-by-bit `first_diff` with one bytewise pass;
3. encode each branch discriminator as a packed byte index and bit tag, while
   preserving the existing one-word branch field;
4. fuse the two traversals performed by `set`;
5. make representative selection constant-time or avoid it on unchanged
   branches;
6. optimize generic `combine` independently, because its arbitrary one-sided
   functions do not permit all of the sharing available to biased union.

## Implementation status

The recommendations are implemented for native OCaml execution in
`PatriciaExtract.v`. The pure Rocq functions and their existing proofs remain
the semantic specification; the optimized realizers extend the explicit
trusted extraction boundary already used for native string access.

The original implementation stages and their decision gates are closed. The
follow-up merge-prefix hotspot is now removed: combine and biased union use a
bounded `agrees_before` worker rather than materializing a `first_diff` result.
The full Rocq/extraction/OCaml oracle suite passes, and the native
comparison benchmark passes at 10,000, 100,000, and 1,000,000 bindings per
input tree. The timing tables in this document are observations from individual
runs; the maintained cross-size measurements and reproduction commands are in
`patricia-bench.md`.

The extracted implementation now:

- performs specialized left- and right-biased union with structural sharing;
- scans `first_diff` bytewise and computes a differing byte bit from its XOR;
- stores branch discriminators as `(byte_index << 4) | tag` tokens;
- performs `set` routing and persistent reconstruction in one descent;
- reads branch samples as constant-time representatives for trees produced by
  the public operations;
- executes generic `combine` without computing or carrying runtime fuel;
- fuses an overlapping leaf's transformation or deletion into the generic
  combine mapping pass;
- traverses membership directly without allocating an intermediate `option`;
- produces `elements` with a linear accumulator traversal;
- propagates failed deletion as `None` and returns the original root without
  rebuilding its routed path;
- uses a closed byte-bounded `agrees_before` scan that returns `bool` directly;
  the source worker has an exact prefix law and is proved equal to logical
  `agrees_before`; and
- uses `String.unsafe_get` only after explicit common-length or byte-index
  bounds establish safety.

`PatriciaTest.ml` independently checks the packed first-difference and bounded
prefix scanners against the logical nine-bit reference encoding for every pair
of one-byte strings and every valid split, covers prefix and long-common-prefix
cases, and continues to validate randomized map results and structural
invariants against reference maps.

A before/after native run with 10,000 five-byte keys on the analysis machine
gave the following observations (not regression thresholds):

| Operation | Before | After |
| --- | ---: | ---: |
| Build | 2.826 ms | 0.834 ms |
| Lookup | 83.4 ns/op | 67.7 ns/op |
| Fresh add | 322.7 ns/op | 113.3 ns/op |
| Existing update | 206.8 ns/op | 122.6 ns/op |
| Remove | 75.1 ns/op | 43.7 ns/op |
| Disjoint left union | 680.9 us, 429,098 words | 0.95 us, 351 words |
| Half-overlap left union | 500.0 us, 425,586 words | 55.1 us, 40,330 words |

The benchmark evidence establishes the original union diagnosis and validates
the native implementation at scale. The initial optimized run still exposed
string-overlap allocation; the next section records how the bounded prefix
scanner removed that cost in the checked 10K and 100K follow-ups.

## Completed follow-up: bounded `agrees_before`

Four-character half-overlap union allocates 40,330, 400,347, and 4,000,362
words at 10K, 100K, and 1M bindings. The approximately four-word-per-binding
progression comes from prefix compatibility checks even though the union's
physical-identity tests reuse the left subtrees.

The previous extracted function was:

```ocaml
let agrees_before left right split =
  match first_diff left right with
  | Some differing -> split <= differing
  | None -> true
```

It scanned beyond `split` when the samples remained equal and materialized an
option result that the caller immediately converts to `bool`. A temporary,
uncommitted generated-code experiment instead compared whole bytes only up to
`split >> 4`, masked the high bits preceding the final tag, and returned a
Boolean directly. On the checked 100K four-character workload it reduced
half-overlap allocation from 400,347 words to 143 words; the single-run time
changed from 0.538 ms to 0.479 ms, and the randomized oracle test passed. The
experiment was initially reverted after measurement. It is now implemented as
`agrees_before_from`/`agrees_before_bounded` in `StringBits.v`; the exact prefix
law and equality with logical `agrees_before` are kernel-checked. The native
packed realization is explicitly documented in `PatriciaExtract.v` and guarded
by the exhaustive packed-split oracle. Fresh checked runs reduced the same
four-character overlap allocation from 40,330 to 128 words at 10K bindings and
from 400,347 to 143 words at 100K bindings. The corresponding single-run times
were 0.051 ms and 0.532 ms; allocation is the stable conclusion.

## Baseline representation and routing

The following sections describe the pre-optimization implementation that was
analyzed to select the changes above.

The runtime tree has three constructors:

```coq
Inductive t (A : Type) : Type :=
| Empty
| Leaf (key : string) (value : A)
| Branch (sample : string) (split : nat) (left right : t A).
```

A branch stores a sample key and a logical split position. It does not store a
string prefix. Lookup ignores the sample and chooses one child from the bit of
the query at `split`:

```coq
| Branch _ split ltree rtree =>
    if bit_at key split then get key rtree else get key ltree
```

Only the reached leaf performs full string equality. This is the source of the
lookup advantage over an ordered tree: an AVL lookup can compare significant
parts of the query against a string at every node, whereas this Patricia tree
normally performs a constant-size routing test at each branch and one complete
comparison at the leaf.

### Prefix-free string bit view

`StringBits.v` maps every byte to nine logical bits:

```text
1, byte-bit-7, byte-bit-6, ..., byte-bit-0
```

The leading `1` is a continuation marker. The end of a string contributes a
`0` marker. Consequently, a proper prefix differs from its extension at the
next marker:

```text
encode("a")    = 1 a7 ... a0 0 ...
encode("a\x00") = 1 a7 ... a0 1 0 ... 0 0 ...
                              ^ first difference
```

This convention is important. Simply treating bytes past the end as zero
would fail to distinguish a prefix from an extension containing zero bytes.
The continuation marker makes empty strings, embedded NUL bytes, and arbitrary
prefix-related byte strings injective in the logical bit view.

The well-formedness predicate states that all keys below a branch agree with
the sample before the split, left keys have a zero at the split, and right keys
have a one. The proof also derives that split positions strictly increase down
the tree. These properties are exactly what a packed critical-bit runtime
representation must preserve.

### Baseline native implementation of `bit_at`

Extraction replaces the recursive Rocq `bit_at` with native OCaml code
equivalent to:

```ocaml
let byte = split / 9 in
let offset = split mod 9 in
if byte >= String.length key then false
else if offset = 0 then true
else ((Char.code (String.get key byte) lsr (8 - offset)) land 1) <> 0
```

This is constant time with respect to string length, but it is not a cheap
single bit test. Every internal node performs integer division and remainder,
a length operation and comparison, a branch for the marker case, and usually
a checked byte load plus shifts. Division and remainder by nine may or may not
be strength-reduced by the particular OCaml compiler and target; that should
be measured rather than assumed.

### Baseline native implementation of `first_diff`

The extracted `first_diff` first evaluates OCaml string equality and, when the
strings are unequal, starts again at logical position zero. It then compares
the strings one logical bit at a time using a local version of `bit_at`.

For unequal strings with a common prefix, the common portion is therefore
examined twice:

1. once by `left = right`, until inequality is established;
2. again by the logical-bit scanner.

The second pass can execute approximately nine iterations per equal byte, and
each iteration computes division and remainder and calls `String.get` for both
strings. The scanner is allocation-free apart from its final `Some`, but
allocation-free does not mean instruction-cheap.

## What the completed benchmark establishes

The benchmark uses OCaml 4.14.3 native code on aarch64 Linux. Its string keys
are fixed-width base-62 strings of lengths three, four, and five. Every result
is checked against `Stdlib.Map`; timings are observations, not regression
thresholds or formal cost results.

The pre-optimization figures in the implementation-status table explain the
selection of the work: lookup was already competitive, ordinary mutations
were slower, and biased union rebuilt whole inputs. The current native
extraction reverses that outcome on the completed 10K-to-1M runs. At 1M,
four-character string keys measured 83.7 versus 121.9 ns/op for lookup, 146.9
versus 222.1 for fresh add, 170.4 versus 206.4 for existing update, and 60.7
versus 105.7 for removal (Patricia versus AVL). The direct-string tree remains
eight words per binding versus AVL's six.

The most decisive pre-bounded-scanner result is union allocation. Across 10K,
100K, and 1M,
disjoint string union allocated 351, 406, and 405 words, while AVL allocated
2,404, 3,620, and 4,940 words. At 1M, half-overlapping string union allocated
4,000,362 words versus AVL's 10,193,264. The low disjoint allocation confirms
that the specialized operation shares input subtrees rather than traversing
and rebuilding every binding.

The later bounded-`agrees_before` follow-up reduced the half-overlap allocation
to 128 words at 10K and 143 words at 100K. A post-follow-up 1M measurement is
not recorded, so the earlier 1M value remains a historical baseline rather
than a current result.

These results support three conclusions:

- Critical-bit routing remains useful for direct byte strings.
- Bytewise first difference, packed routing, and a one-descent update remove
  the previously identified ordinary-mutation pathologies without enlarging
  the retained representation.
- Specialized biased union is architecturally necessary; primitive routing
  micro-optimizations alone could not have removed the old whole-tree union
  path.

### Why the retained size is about eight words per binding

A non-empty full binary Patricia tree with `N` leaves has `N - 1` branches.
With the extracted OCaml constructor layout:

- a `Leaf (key, value)` block occupies approximately one header plus two
  fields, or three words;
- a `Branch (sample, split, left, right)` block occupies approximately one
  header plus four fields, or five words.

The tree nodes therefore occupy approximately:

```text
3N + 5(N - 1) = 8N - 5 words.
```

This matches the measured asymptote of eight words per binding. It also gives
an important design constraint: replacing `split` with separate `byte` and
`mask` fields would add roughly one retained word per binding. A packed
one-integer discriminator avoids that regression.

## Cost by operation

### Lookup and membership

`get` executes one `bit_at query split` per visited branch, then one string
equality at the reached leaf. `mem` now follows the same route directly and
returns a Boolean at the leaf, avoiding the intermediate `option` allocated by
successful `get` calls.

The relevant costs are:

- tree depth in distinct critical positions;
- decoding `split` into byte and offset at every branch;
- random byte access and branch prediction;
- final full equality, particularly for an absent key routed to a leaf with a
  long common prefix.

Unlike the positive-integer tree, string-tree depth is not bounded by a fixed
machine word width. It is bounded by the represented key-bit positions and can
grow with maximum key length. Compression prevents unary paths, but adversarial
sets can still contain many distinct critical positions along one route.

### Existing-key `set`

The proof-side specification's original `set` performs:

1. `routed_key key m`, which traverses from root to leaf;
2. `first_diff key routed`, which scans the query and leaf key;
3. when the strings are equal, `replace key value m`, which traverses the same
   route again and allocates the persistent replacement path.

The extracted native `set` instead descends once, using `Fresh_key` to carry a
fresh discriminator back up the visited path. Existing updates rebuild that
one path, and insertions are spliced while unwinding. This removes the
two-traversal behavior while leaving the proof-side function as the semantic
specification.

### Fresh-key `set`

Fresh insertion in the proof-side baseline also routes twice:

1. `routed_key` finds the leaf selected by existing critical bits;
2. `first_diff` finds the new key's first differing logical bit;
3. `insert_at` starts again at the root, descends to the correct insertion
   position, and allocates the persistent path.

The second descent was an artifact of that organization, not of the data
structure. The native implementation retains the path on the call stack and
unwinds after discovering the first difference.

### Removal

`remove_changed` performs one routed traversal and returns `None` when the key
is absent, allowing public `remove` to return the original root. A successful
deletion propagates `Some changed` while reconstructing the path. The smart
`branch` collapses a node if either child becomes empty. When both children are
non-empty, the string implementation calls `representative ltree` to select a
new sample. `representative` descends toward a leaf rather than using the
sample already stored in a branch.

That representative descent can add work at every reconstructed ancestor. In
native code, branches produced by the public operations cache a resident key,
so extracted `representative` returns the stored sample in constant time. The
pure function remains the conservative specification for arbitrary values made
with exposed constructors.

### Generic combine and biased union

The proof-side public `combine` calls:

```coq
combine_fuel (S (size a + size b)) f a b
```

Computing the fuel traverses every node before merging. The branch cases then
use `map_left` and `map_right` for one-sided subtrees. Those operations must
visit every binding for an arbitrary combining function because it may change
or delete one-sided values.

The extracted direct recursion now delegates leaf/tree and tree/leaf cases to
proved source workers. When the leaf key overlaps, a key-aware `map_filter`
applies the two-sided result during the required whole-tree transformation,
instead of materializing that binding and then traversing a second path to
replace or remove it. The absent-key case retains the ordinary mapped-tree
insertion path.

Biased union does not have that requirement. For left-biased union, a subtree
that occurs only on the left or right can be returned unchanged, and two
structurally disjoint trees can be joined beneath one new branch. Expressing
biased union through generic `combine` erases this information and forces
mapping and reconstruction. The nearly key-length-independent union allocation
in the benchmark is consistent with node rebuilding dominating string work.

## Optimization rationale and current status

The seven subsections below preserve the rationale that led to the current
native implementation. Their prescriptive wording is historical; remaining
proof and refinement work is tracked under N1 and N2 in
[`patricia-todo.md`](patricia-todo.md).

### 1. Specialized structurally sharing biased union

**Status:** implemented and benchmarked in native extraction; source-level
algorithm refinement and formal sharing claims remain open under N2/N4.

**Expected impact:** decisive for union; little or no effect on standalone
lookup and mutation.

Define `union_left` and `union_right` as specialized tree algorithms rather
than calls to generic `combine`. For left-biased union, the important cases
are:

- empty on either side: return the other tree directly;
- disjoint prefixes: join the original trees directly;
- containment: recurse only into the potentially overlapping child and reuse
  the other child;
- equal branches: recurse pairwise;
- leaf overlap: retain the left value without mapping either whole tree.

The algorithm should not compute `size`, call an identity-shaped `map_left` or
`map_right`, or reconstruct a branch whose recursive child is physically
unchanged. A well-founded measure can live in `Prop`, allowing extraction to
erase termination evidence.

This option addressed the dominant disjoint-union time and allocation gap. No
routing micro-optimization is in the same impact class.

The general string `combine` law is now proved. The specialized union proof
remains distinct because its native algorithm has identity one-sided behavior
and fewer filter-collapse cases.

### 2. Scan `first_diff` byte by byte

**Status:** implemented natively, with a proved safe source model. Native byte,
`Char.code`, XOR, and unsafe-access refinement remains open under N1.

**Expected impact:** high for build and fresh insertion, potentially material
for merge; no direct effect on successful lookup.

The first differing logical position can be computed without examining nine
logical bits per byte:

1. scan the common byte range once;
2. if the first unequal bytes are at index `i`, compute
   `xor = code left.[i] lxor code right.[i]`;
3. locate the most-significant set bit of the eight-bit `xor`;
4. return the corresponding data-bit discriminator;
5. if all common bytes agree and the lengths differ, return the continuation
   marker at the end of the shorter string;
6. if both length and contents agree, return `None`.

In terms of the current logical position:

```text
prefix difference at byte i: split = 9 * i
data difference at byte i:   split = 9 * i + 1 + leading_zeroes_8(xor)
```

An eight-entry shift loop or a 256-entry lookup table can find the differing
bit without relying on a particular OCaml version's integer-leading-zero API.
The byte scan itself should handle equality, avoiding the current unequal-case
prepass from `left = right`. A physical-equality check may remain as a fast path
for the same string object.

This produces exactly the existing prefix-free bit result; it changes the
algorithm, not the finite-map semantics. There are two verification choices:

- retain the pure Rocq definition and install a faster extraction constant;
  this is the smallest implementation change but enlarges the already trusted
  extraction boundary;
- define the bytewise scanner in Rocq and prove its result equivalent to
  `first_diff`; this provides a better verified baseline, after which only the
  native byte and bit primitives remain trusted.

### 3. Pack byte index and discriminator into the branch integer

**Status:** implemented natively. The codec and safe packed operations are
proved in `NativeRefinement.v`; primitive finite-width refinement remains open
under N1.

**Expected impact:** material for lookup and every routed mutation; neutral on
asymptotic behavior; no retained-size increase if packed.

The semantic split position contains two pieces of information:

- byte index `split / 9`;
- tag `split mod 9`, where zero denotes the continuation marker and `1..8`
  denote data bits from most to least significant.

Store those pieces in an OCaml immediate integer using, for example:

```text
token = (byte_index << 4) | tag
```

Four tag bits are sufficient for `0..8`. Numeric token order agrees with
logical split order because every byte reserves a monotonically ordered block
of sixteen tags. Thus the existing comparisons on split positions can be
replaced with token comparisons, provided constructors only produce valid
tags.

Routing becomes:

```text
byte = token >> 4
tag  = token & 0xF

if tag = 0:
    direction = byte < String.length key
else:
    direction = byte < String.length key
                and (code key.[byte] & (1 << (8 - tag))) != 0
```

The length condition preserves the prefix-free convention. For a valid data
split in a well-formed tree, every resident descendant should have that byte,
but a query can be shorter, so lookup must retain the bounds check.

Packing uses shifts and masks instead of division and remainder and keeps the
branch at four fields. Storing `byte_index` and `mask` as two separate fields
would increase the retained representation from approximately eight to nine
words per binding, contrary to the existing memory result.

On the proof side, it is cleanest to introduce a discriminator type or a
valid-token predicate and prove:

- packing/unpacking correctness;
- equivalence of token routing to `bit_at key split`;
- preservation of split ordering;
- equivalence of the bytewise first-difference result to the first differing
  logical bit.

Using multiplication by nine in the scanner only once per insertion is much
less important than eliminating division by nine from every branch visit. A
fully token-native scanner can avoid even that multiplication.

### 4. Fuse routing and persistent reconstruction in `set`

**Status:** the one-descent worker is proved and retained as an extracted
experiment. The public setter now uses ordinary extraction of the proved
two-descent definition, which avoids both handwritten exception control flow
and the one-descent worker's per-level result allocation.

**Expected impact:** high for update and useful for insertion; proof and
implementation complexity are higher than the primitive optimizations.

A one-descent algorithm can recurse to the routed leaf, compute the first
difference there, and propagate one of two outcomes while unwinding:

- existing key: rebuild the visited path with the new leaf;
- fresh key with discriminator `d`: bubble an insertion request upward across
  every visited ancestor whose split is greater than `d`, splice it immediately
  below the nearest ancestor whose split is less than `d`, and place it above
  the root if no such ancestor exists.

Because well-formed descendant splits strictly increase, the unwind has enough
information to find the insertion point without routing from the root again.
An explicit zipper is another formulation, but it allocates path frames. A
recursive result type may allocate transient outcome blocks unless extraction
optimizes them, so both CPU time and allocation must be measured.

The proof should reuse `wf_splits_ordered` and the existing `insert_at` lemmas.
A sensible development path is:

1. implement the fused algorithm alongside `set`;
2. prove it extensionally equivalent to the already-proved `set` operation on
   well-formed trees;
3. prove well-formedness either through equivalence plus structural lemmas or
   directly;
4. benchmark before replacing the public definition.

### 5. Make representative access constant-time

**Status:** implemented natively, and cached-sample residency is proved.
Representative independence for native consumers remains open under N2.

**Expected impact:** likely useful for removal, join, and union; magnitude is
not yet measured.

Every `Branch` already stores `sample`. The strengthened `wf_branch` now states
both the routing-prefix conditions and `resident sample (Branch ...)`, meaning
lookup of the cached sample succeeds. Every branch-building preservation proof,
including deletion, filtering, insertion, combine, and biased union, maintains
that property. `wf_cached_sample_resident` exposes it directly.

There are three implementation choices:

1. strengthen `wf_branch` so the stored sample is proved to be a resident key,
   maintain that cache through deletion/filtering, and make
   `representative (Branch sample ...) = Some sample`;
2. have deletion and filtering return a representative with the rebuilt tree;
3. avoid recomputing the sample when the old sample is known not to have been
   removed, and search only when it becomes invalid.

The first choice is now implemented. It gives the simplest runtime read and
does not increase the node size because the sample field already exists. The
remaining refinement obligation is subtler than residency: the pure
representative descent and cached read may choose different resident keys, so
native consumers must be shown independent of that choice.

An alternative is to remove the sample field and find representatives by
descent. That would reduce tree nodes toward seven words per binding, but it
would make merge-prefix decisions and representative selection more expensive.
It should not be selected without workloads showing retained memory is more
important than merge and mutation latency.

### 6. Remove runtime fuel from generic `combine`

**Status:** implemented by the native realizer. A well-founded source worker
and equivalence with `combine_fuel` remain open under N2.

**Expected impact:** high for all generic combines, but insufficient by itself
for fast biased union.

Move termination to a well-founded recursion whose accessibility evidence is
in `Prop` and erased by extraction. This removes the unconditional `size a +
size b` traversal.

Generic combine may still have to transform all bindings that occur on only one
side. For example, `f (Some v) None` may change `v` or return `None`. Therefore,
generic combine cannot generally reuse those subtrees. This is why specialized
biased union remains necessary even after fuel removal.

String combine also repeatedly invokes `agrees_before`, which computes a first
difference between branch samples. The bytewise scanner improves this directly.
A later optimization could return richer prefix-comparison information once
per branch pair, rather than separately asking agreement and then routing a
sample, but its value should be measured after the larger changes.

### 7. Use unchecked native byte access only as a final micro-optimization

**Status:** implemented behind explicit length/index guards. Its correspondence
to the safe source byte model remains open under N1.

**Expected impact:** small to moderate after packed routing; increases the
trusted native boundary.

After explicitly checking `byte < String.length key`, extracted code could use
`String.unsafe_get`. This may avoid a redundant bounds check if the compiler
does not eliminate it. It should be attempted only after inspecting generated
native code or measuring a focused `bit_at` benchmark. It does not change the
algorithm and should not precede bytewise scanning, packed discriminators, or
traversal fusion.

## Alternatives that change the data-structure tradeoff

### Hash routing

Routing on a string hash would make routing independent of key bytes after the
hash is computed or cached, but it introduces collisions and loses the
canonical critical-prefix structure used by fast Patricia merge. Cached hashes
also add a word to each key or leaf unless supplied externally. A HAMT can be a
good map, but it is a different representation and proof project rather than a
small optimization of this tree.

### Multiway byte tries or adaptive radix trees

A byte-oriented radix tree can examine a byte rather than a bit and may reduce
depth. Dense 256-way nodes waste substantial space; adaptive node layouts
reduce that waste at the cost of multiple representations and much larger
proof and extraction complexity. They may be appropriate if very long keys and
lookup throughput dominate, but the current bitwise tree already beats AVL
lookup while using predictable binary nodes.

### Encoding entire strings as integers

The direct representation intentionally avoids converting whole strings to
integers. An injective arbitrary-length encoding requires unbounded integers or
another variable-length representation, adds conversion/caching costs, and
does not remove the need to handle prefixes and embedded zero bytes. The
positive-integer benchmark should not be read as evidence that whole-string
integer conversion would inherit the same results.

### Removing samples to save one word per branch

This can plausibly reduce retained nodes from approximately eight to seven
words per binding, but it makes prefix/merge decisions depend on a
representative descent or on separately stored prefix data. It trades away
time in precisely the operations for which the current design is optimized.
Treat it as a memory-profile variant, not the default performance plan.

## Verification and trusted-boundary implications

The current custom `Extract Constant` definitions for `bit_at` and
`first_diff` are trusted refinements: Rocq proves the pure functions, not that
the handwritten OCaml implementations are equivalent. The two tracks below
explain the design choice; N1 and N2 in `patricia-todo.md` contain the active
refinement tasks.

### Minimal-change optimized track

- Keep the existing logical `nat` split and proofs.
- Replace only the extracted `first_diff` and possibly `bit_at` implementations.
- Differential-test the optimized functions against a pure extracted backend.

The third step is now implemented by `PatriciaReferenceExtract.v` and
`PatriciaDifferentialTest.ml`. The reference retains the executable Rocq
algorithms while sharing the standard native integer/string mappings. The test
translates packed positions to logical ranks and compares low-level bit
operations as well as complete map workloads. This detects disagreements but
does not reduce the trusted base by itself.

This is fast to implement but does not reduce the trusted computing base. A
packed discriminator is awkward on this track because the extracted tree field
would no longer have the same direct representation as the proof-side `nat`
unless packing is consistently refined everywhere.

### Explicit discriminator/refinement track

- Define a proof-side critical discriminator with marker and data-bit cases, or
  define valid packed tokens and their logical rank.
- Prove routing equivalent to the current prefix-free `bit_at`.
- Prove bytewise first difference returns the least differing discriminator.
- Restate branch ordering using discriminator order.
- Extract the discriminator to one native OCaml integer.

This requires more proof migration but makes the runtime design explicit and
keeps malformed tag values out of the proved model. It is the stronger choice
if the optimized native backend is intended to support a formal-verification
claim rather than remain an audited foreign refinement.

`NativeRefinement.v` now provides the valid packed-token model, codec order,
safe packed routing, and a source bytewise first-difference proof. The open part
is the connection to bounded OCaml integers, byte access, `Char.code`, XOR, and
the optimized map realizers; those obligations are N1 and N2 in
`patricia-todo.md`.

The supported extracted map types are now abstract behind `PatriciaMap` and
`StringPatriciaMap`. Raw constructors remain available only in explicitly
internal generated modules used by structural validation.

## Validation record

The following records completed empirical validation of the native extraction
boundary. It does not close the formal refinement obligations in N1 and N2.

### Build, proof, and oracle validation

`make -C patricia all` completed successfully again on 2026-08-30. It
recompiles the Rocq proof files and both extractions, audits every top-level
proof declaration with `Print Assumptions`, rebuilds the bytecode clients, and
runs both `PatriciaTest.ml` and the optimized/reference differential suite. The audit
reports all 247 declarations closed under the global context.
The test suite differentially checks the packed `first_diff` scanner against
the logical nine-bit model for all 65,536 pairs of one-byte strings. It also
covers empty strings, prefixes, embedded NULs, non-ASCII bytes, and long
common prefixes, then checks randomized map behavior and structural routing
invariants against reference maps.

### Native scale validation

The following commands all completed with `Patricia comparison benchmark: ok`:

```sh
make -C patricia benchmark
PATRICIA_BENCH_SIZE=100000 make -C patricia benchmark
PATRICIA_BENCH_SIZE=1000000 PATRICIA_BENCH_STRING_LENGTHS=4,5 \
  make -C patricia benchmark
```

The historical scale checks passed. For disjoint union, integer Patricia
allocation was 288, 379, and 486 words at 10K, 100K, and 1M bindings
respectively; the four-character string variant used 351, 406, and 405 words.
This is a
join-spine-sized cost, rather than work proportional to all bindings. At 1M,
string half-overlap used 4,000,362 words versus AVL's 10,193,264, and all
result maps were checked against `Stdlib.Map`.

The retained-size result was also stable: the direct-string tree stayed at eight
words per binding at every completed scale. The current measurements, machine
details, and full tables are maintained in `patricia-bench.md`; they are
observations, not portable regression thresholds.

### Closed implementation stages

1. **Union architecture:** extracted `union_left`/`union_right` are
   specialized, return empty and unchanged subtrees directly, join disjoint
   trees, and do not compute runtime fuel.
2. **String primitives:** the packed byte/tag discriminator and bytewise-XOR
   `first_diff` are installed. Exhaustive one-byte differential tests plus
   prefix, NUL, and long-prefix cases validate the required routing result.
3. **Mutation traversal:** extracted `set` performs one routed descent and
   reconstructs or inserts while unwinding. The randomized oracle and
   structural tests exercise both fresh and existing-key behavior.
4. **Representative and generic combine:** public-operation branches use their
   cached samples as constant-time representatives, and extracted `combine`
   recurses directly without carrying proof-side fuel.
5. **Bounded prefix checks:** source combine calls the proved bounded worker;
   its packed native realization compares only bytes and high bits before the
   split and returns a Boolean without per-call allocation.

The previously proposed primitive microbenchmarks and side-effecting internal
counters remain diagnostic tooling rather than completion gates. Allocation
scaling was sufficient to isolate and remove the `agrees_before` cost; a
physical-sharing counter would still be useful when expanding the union
workloads beyond ordered ranges. The oracle checks validate exposed behavior
empirically, not end-to-end formal refinement of the native realizers.

## Final recommendation

Keep bit-level Patricia routing: it handles arbitrary byte strings correctly
and retains a measured lookup advantage. The native implementation now uses a
packed critical-byte token, bytewise-XOR first-difference discovery, a
source-extracted two-descent `set`, cached constant-time representatives,
fuel-free generic
combine, a bounded prefix scanner, and structurally sharing biased union. The
direct-string biased-union and extensional-`beq` laws are now proved, as is
strong sorting of `elements` by the prefix-free bit-stream lexicographic
order. Lookup-based finite-map extensionality is also packaged for both key
variants. The extracted backends are now internal modules behind abstract
`PatriciaMap` and `StringPatriciaMap` interfaces. The integer wrapper now admits
only validated positive native keys. Their public generic-`combine` APIs split
the represented-key cases into `left_only`, `right_only`, and `both` callbacks;
absence from both maps is handled internally as absence, enforcing the proof
contract by construction. A separately packed, proof-aligned extraction is now
retained and compared with the optimized backend during every normal build.

The completed scale runs confirm the key architectural result: specialized
biased union fixes the former whole-tree traversal and rebuilding path, while
the string-operation changes preserve the eight-word representation and pass
the extraction, differential, structural, and map-oracle checks. The measured
string-overlap allocation is constant-sized in the checked 10K and 100K
follow-ups. The principal remaining limitation is that packed-position and
other OCaml extraction overrides are trusted refinements of the pure Rocq
specification rather than proved refinements inside Rocq. Those obligations,
and optional future benchmark or representation work, are tracked in
`patricia-todo.md`, including benchmark hardening under N6.

## Source basis

- `StringBits.v`: prefix-free bit encoding, `bit_at`, `first_diff`, and their
  specifications.
- `StringPatricia.v`: tree layout, lookup, two-pass `set`, removal,
  representatives, generic combine, and biased-union definitions.
- `StringPatriciaProof.v`: routing invariant, split ordering, and current
  correctness coverage.
- `PatriciaExtract.v`: native OCaml realizations of string bit access,
  first-difference scanning, and bounded prefix comparison.
- `PatriciaReferenceExtract.v`: proof-aligned reference extraction without
  Patricia-specific custom realizers.
- `PatriciaDifferentialTest.ml`: direct optimized/reference comparisons for
  low-level string bits and full integer/string map workloads.
- `PatriciaBenchmark.ml`: benchmark workloads, correctness checks, timing, and
  allocation methodology.
- `patricia-bench.md`: recorded 10K through 1M baseline results and the
  completed bounded-`agrees_before` follow-up.
- `patricia.md`: verification review and trusted-boundary analysis.
- `patricia-todo.md`: active decisions, refinement work, optional performance
  work, and completion gates.
