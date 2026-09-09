# Standalone Patricia-tree sketch

This directory is intentionally self-contained. It contains two compressed
Patricia-tree sketches:

- `Patricia.v`: big-endian Patricia trees proved over unbounded positive keys
  and extracted as a native OCaml `int`-key API.
- `StringPatricia.v`: direct Patricia trees over byte strings. Branches store
  differing-bit positions; lookups route to one leaf and compare the key once.
  Strings are not converted to integers.

The supported contracts, theorem checklist, and trusted computing base are in
[`SPECIFICATION.md`](SPECIFICATION.md). The verification review and active
tracker are in [`patricia.md`](patricia.md) and
[`patricia-todo.md`](patricia-todo.md). The detailed unverified-code inventory,
strategies and separate native-verification tracker are in
[`patricia-native-verification.md`](patricia-native-verification.md).
Publication citations and local PDF provenance are indexed in
[`papers/README.md`](papers/README.md).

Run:

```sh
make
```

For a native-code comparison with OCaml's standard-library AVL tree and hash
table, run:

```sh
make benchmark
```

To profile the ordinary extraction of the proof-side definitions separately,
run `make reference-profile`. It checks every measured result against
`Stdlib.Map`; use the same `PATRICIA_REFERENCE_PROFILE_SIZE` and compiler
configuration when comparing its output with the optimized benchmark.

The comparison verifies each measured Patricia and `Stdlib.Hashtbl` result
against `Stdlib.Map`. It reports build, lookup, membership, traversal
(`elements`), add, update, and present/absent remove time, retained heap words
per binding, and allocated words. Failed Patricia deletions additionally check
physical root identity. It also reports checked generic-combine leaf/tree
transformations and deletions, plus allocation and time for left-biased unions
with disjoint and half-overlapping inputs. Integer keys; independent 3-, 4-,
and 5-character ASCII-alphanumeric string key sets; and a variable-length
string case are measured separately.
The default is 10,000 bindings per input tree; set `PATRICIA_BENCH_SIZE` to
change it (the three-character case permits at most 119,164 bindings per
input tree, because each benchmark also constructs a disjoint tree).  Reported
figures are benchmark evidence, not machine-independent pass/fail limits or
formal complexity proofs. The default fixed-length cases omit lengths too
short for the requested pair of disjoint input ranges. Set
`PATRICIA_BENCH_STRING_LENGTHS` to a comma-separated subset of positive key
lengths to select fixed-width cases explicitly. The variable-width case uses
base-62 strings bounded by `PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH`
(default `128`); increase that bound when its key space is too small.

`PatriciaBits.v` fixes the proof-side positive-key convention. `StringBits.v`
defines the prefix-free string bit view (a continuation marker plus eight bits
per byte and an end marker), so empty strings, embedded zero bytes, and prefix
keys are distinct. `NativeRefinement.v` records the supported 62-bit native
key domain and the codec between logical string-bit positions and the packed
native tokens. It includes a native byte-code-array model for OCaml strings,
proves byte length/access/bounds and guarded-access laws, and proves the packed
`bit_at` model correct. Connecting those laws to each actual indexed OCaml loop
and its guards remains a target-level obligation. In particular, the packed
bounded-prefix loop still needs its own refinement proof. OCaml's string,
`Char.code`, and integer primitives also retain explicit foreign contracts.
`PatriciaExtract.v` generates implementation backends under
`patricia/extracted/`; the build names the map modules `PatriciaInternal` and
`StringPatriciaInternal`. `PatriciaReferenceExtract.v` separately generates
the executable Rocq definitions without Patricia-specific custom realizers,
packs them under `PatriciaReference`, and links them beside the optimized
modules for deterministic differential testing. The supported OCaml interfaces
are the handwritten `PatriciaMap` and `StringPatriciaMap` modules. Their `.mli`
files make map types abstract and expose only smart map operations; generated constructors, routing
metadata, packed string positions, fuel/change workers, and merge helpers stay
behind that boundary. The structural oracle intentionally uses the internal
modules, while the comparison benchmark uses only the abstract interfaces.
Integer-map keys have the abstract type `PatriciaMap.Key.t`; `Key.of_int` and
`Key.of_int_exn` are the only public constructors and reject zero and negative
integers. `Key.to_int` provides explicit conversion back to a native integer.
Public generic combination uses a `combiner` record with separate `left_only`,
`right_only`, and `both` callbacks. The wrappers supply `None` themselves for
keys absent from both inputs, making the proof condition
`f None None = None` unrepresentable through the supported interface.

Native extraction maps integer keys, prefixes, masks,
and routing operations to OCaml `int`. String branch discriminators are packed
as a byte index and four-bit tag, first differences are found in one bytewise
pass, bounded prefix checks scan only through their split, public string updates
use the proved two-descent worker, branch samples provide constant-time
representatives, and biased unions
share one-sided and disjoint subtrees.

The positive-key proof file currently establishes, without axioms:

- empty/singleton lookup, `mem`, same-key and different-key `set`, and
  key-aware `map` laws;
- representative soundness and lookup/`wf` correctness for compatible and
  disjoint `join` operations;
- simultaneous lookup correctness and `wf` preservation by `set` and bulk
  `of_list` (whose first duplicate binding wins);
- general `remove` lookup correctness, `wf` preservation, and structural
  identity when the removed key is absent;
- lookup correctness and `wf` preservation by `map_filter`, `map_left`, and
  `map_right`;
- lookup correctness and `wf` preservation for fused left- and right-leaf
  generic-combine workers;
- `fold` agreement with `elements`;
- `elements` soundness, completeness on `wf` trees, and unique keys;
- lookup-based finite-map equivalence, its equivalence-relation laws, its
  exact correspondence with binding membership, and extensional correctness
  of `beq` on `wf` trees;
- sufficiency of the public combine fuel bound for every recursive call shape;
- general lookup correctness and `wf` preservation by `combine_fuel` and the
  public `combine`, for the standard finite-map condition
  `f None None = None`;
- highest-differing-bit prefix agreement and bit separation.

The direct-string proof files currently establish, without axioms:

- injectivity of the prefix-free bit view, including character-bit
  injectivity and the fact that bits past the encoded end are false;
- an exact specification of the bounded first-difference scan: unequal
  strings have a differing position, the bits differ there, and every earlier
  bit agrees;
- the logical specification of `agrees_before`, an exact specification of its
  bounded scanner, and a proof that the two Boolean results are equal;
- a structural routing invariant for string trees and preservation of that
  invariant by smart branch collapse, `remove`, key-aware `map`, and general
  `set`, including fresh-key insertion; every branch's cached sample is now a
  resident binding under the same invariant;
- strict increase of descendant string split positions, derived from that
  routing invariant;
- representative and routed-leaf soundness;
- two-way agreement between `get` and `elements` on well-formed trees,
  completeness of lookup, unique element keys, unique bindings, and strong
  sorting by the prefix-free bit-stream lexicographic order;
- the general lookup specification for `remove`, structural identity for an
  absent key, plus the corresponding `elements` filtering specification;
- the unconditional `set` lookup law and well-formedness preservation,
  including fresh and existing keys, plus the corresponding first-binding-wins
  `of_list` law;
- `fold` agreement with `elements`, the key-aware `map` lookup law, and
  well-formedness/lookup laws for `map_filter`, `map_left`, and `map_right`
  (the latter two under `f None None = None`).
- well-formedness and lookup laws for fused left- and right-leaf
  generic-combine workers under `f None None = None`.
- sufficiency of the public combine fuel bound for every recursive-call shape.
- simultaneous lookup correctness and well-formedness for `combine_fuel` and
  public `combine` under `f None None = None`.
- pointwise and lookup-extensional correctness of string `beq` on `wf` trees.
- lookup-based finite-map equivalence, its equivalence-relation laws, its
  exact correspondence with binding membership, and equivalence with an
  equality-reflecting string `beq`.
- strong sorting of string `elements`: every earlier key precedes every later
  key at their first differing prefix-free logical bit (`false` before
  `true`).

The normal build discovers every top-level `Lemma`, `Theorem`, and `Corollary`
in the source proof modules, including `NativeRefinement`, then runs `Print
Assumptions` on each. Validation fails on reported axioms, Rocq errors, or any
mismatch between discovered declarations and results closed under the global
context.

`join_separated_correct_wf` proves the string-tree join law under explicit
prefix/bit-separation preconditions, including filtered empty sides. The
specialized left- and right-biased union laws are derived from the generic
combine theorem.

It then runs deterministic randomized OCaml tests against reference maps. The
positive suite exercises point updates, removal, generic and deletion-capable
combines, both biased unions, element ordering, routing/canonicality, and
keys at every native bit boundary through `max_int`. The string suite checks
the same map operations and structural routing invariants over empty strings,
embedded NUL bytes, prefix-related strings, non-ASCII bytes, long common
prefixes, and generated arbitrary byte strings. These are executable tests,
not Rocq proofs or complete validation of the custom extraction constants.
The normal `make` also compares the optimized and proof-aligned backends over
map updates, removals, filtering, generic combination, both biased unions,
folding, equality, and lookup. It directly compares string bit operations by
encoding logical positions to native packed tokens and decoding first
differences back to logical positions.

This is intentionally a standalone design sketch. Constructors remain visible
only in the explicitly internal generated modules used by the structural tests;
supported clients use abstract map types. The integer proofs use unbounded
positive keys, while extraction uses bounded OCaml `int`.
`PatriciaMap.Key` restricts supported clients to the representable positive
domain `1 .. max_int`; the finite-width refinement itself remains trusted rather
than proved. The string tree uses native OCaml strings and proof-side
logical bit positions; native extraction represents positions as packed
byte/tag integer tokens. General `combine` extracts directly from proved
structural recursion; the public biased unions still use handwritten
realizers. These native refinements form an explicit performance/correctness
boundary. For the source models of those unions, Rocq now
checks every equal-header and containment reconstruction under the sole
positive-direction contract that OCaml `changed == original` implies identical
current lookups. This is deliberately stronger than the portable documented
`==` guarantee for non-mutable values (`compare = 0`), so connecting it to the
runtime/compiler remains an external obligation. Refinement of the actual
handwritten recursive bodies and their dependencies is also open. The source
proofs and abstract heap bridge do not establish target execution, allocation
or sharing guarantees; the separate native-verification tracker records these
remaining steps.
