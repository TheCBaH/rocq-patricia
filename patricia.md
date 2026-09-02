# Patricia-tree verification review

Review date: 2026-08-30

The supported public contracts, theorem checklist, and trusted computing base
are fixed in [`SPECIFICATION.md`](SPECIFICATION.md). The active implementation
plan and status tracker are maintained separately in
[`patricia-todo.md`](patricia-todo.md). Performance analysis is in
[`patricia-str.md`](patricia-str.md), and measured results are in
[`patricia-bench.md`](patricia-bench.md).

## Scope and verdict

The review covers the standalone implementation under `patricia/`: the
positive-integer Patricia tree, the direct byte-string Patricia tree, their
Rocq proofs, OCaml extraction directives, and the randomized OCaml test
harness.

The implementation is a strong executable and proof development. Both pure
source models have functional-correctness coverage for the current custom map
API, including first-binding-wins bulk `of_list`, and both extracted
implementations behaved correctly in the supplied tests and in additional
fuzzing. The supported OCaml wrappers now enforce the
representable structural, positive-key, and combine preconditions. It is not
yet a complete end-to-end formally verified mergeable-map library, however:
the optimized native extraction remains a second implementation rather than a
proved compilation or refinement of the Rocq definitions.

The verification claim must therefore be split into three layers:

| Layer | Current status |
| --- | --- |
| Pure positive-key Rocq model | Kernel-checked functional map laws, including general `combine` and finite-map extensionality, with no project axioms found in the inspected theorem closure |
| Pure direct-string Rocq model | Lookup, update, removal, ordered traversal, filtering, structural invariants, general `combine`, biased unions, and finite-map extensionality are proved |
| Extracted native OCaml | Extensive oracle, invariant, and optimized-versus-proof-aligned differential testing passes, but the standard numeric/string mappings and remaining explicit handwritten realizers are trusted; neither their refinement nor the Rocq-to-OCaml compilation pipeline is proved here |

Consequently, “formally verified” is accurate for the stated theorems about the
pure definitions. It is not yet accurate as an end-to-end claim about the
optimized OCaml library.

## Validation results

The normal validation gate was rerun successfully on 2026-08-30. The following
checks passed:

- `make -C patricia`, including all Rocq proof files, extraction, OCaml
  compilation, and the deterministic randomized oracle test;
- a source scan found no `Admitted`, `admit`, `Axiom`, aborted proof, or similar
  unresolved proof escape in the Patricia sources;
- the source-driven `Print Assumptions` audit discovered all 247 top-level
  lemmas, theorems, and corollaries across the bit-specification, map-proof,
  and native-representation modules, and reported each closed under the global
  context;
- additional integer fuzzing used keys across the positive OCaml `int` range,
  including high-bit boundary values, and checked lookup, elements, merge, and
  routing invariants;
- additional string fuzzing used arbitrary byte strings, including non-ASCII
  bytes, and checked lookup, elements, merge, branch separation, prefix
  agreement, non-empty children, and increasing split positions.

No functional counterexample was found for the public map operations exercised
by these checks. There is, however, a deliberate pointwise mismatch in the raw
low-level API: pure `bit_at "ab" 9` is `true` (the second byte's continuation
marker), while extracted `StringBits.bit_at "ab" 9` is `false` because native
position 9 is an invalid packed tag and logical position 9 is represented by
token 16. Internal map operations consistently use packed tokens, but the
separately exported function does not retain its source-level type contract.
Fuzzing is supporting evidence only; it does not close the proof gaps described
below.

## Review findings

### 1. Native merge now avoids fuel and biased union shares structure

The public Rocq definitions now use direct nested structural recursion. The
outer fixpoint consumes the left tree; when that tree is held fixed, an inner
fixpoint consumes the right tree.
`combine_structural_eq_combine_fuel` proves that each worker exactly agrees
with the retained fuelled reference at every sufficient fuel bound. The native
extraction now retains those direct structural `combine` definitions, so it
does not compute the bound at runtime or substitute a handwritten merge. Its
leaf/tree cases delegate to source-level workers with proved lookup and
well-formedness laws, fusing an overlapping replacement into the mapping pass.
Both public wrappers currently call the handwritten native biased-union
realizers, which use physical identity to reuse an unchanged original branch
(`union_right` reverses its arguments). The extracted changed-result workers,
including the fuel worker now proved equal to them, remain the source-level
functional oracle. Disjoint prefixes are joined immediately, one-sided
subtrees are reused, and only a changed recursive path is rebuilt.

`union_left_native_default` now mirrors that custom recursion in Rocq and
extracts with only `native_same` mapped to `(==)`. It restores root reuse but
still allocates roughly 0.8M words for 100K half-overlap inputs and 1.6M for
equal inputs, owing to generated helper/closure traffic; the 365/81 and 26/26
word legacy integer/string results remain decisively lower. The public wrappers
therefore retain the handwritten export while this candidate is improved.
For the integer backend, `union_left_native_correct_wf` now assembles the
per-branch reuse certificates into whole-worker well-formedness and left-biased
lookup laws under the sole positive-direction `native_same_sound` premise.
The direct-string theorem of the same name carries cached-sample residency
through the same assembly. Neither source theorem establishes the OCaml `(==)`
contract.
The closure-free fuel-shaped native candidate was worse still (1,200,993 /
1,200,634 words for half overlap and 2,400,919 / 2,400,891 for equality),
because its generic physical-equality callback is invoked through the recursive
worker. Inlining that callback and the root/child reconstruction checks in the
single fuel worker improves the corresponding results to 1,100,853 / 1,100,598
and 2,200,677 / 2,200,707 words, respectively, but remains far above both the
nested candidate and the legacy implementation. This rules out direct source
inlining as the relevant generated-code improvement; changing the recursion
measure alone is not useful either.
Making `(==)` extraction-inline and compiling the diagnostic with
`ocamlopt -inline 1000` made no material difference; this OCaml 4.14.3 build
does not include Flambda. The practical next boundary is consequently a small
handwritten recursive skeleton (with source-verified called primitives), or a
separately verified target-language implementation.

The 10,000- and 100,000-binding benchmark checks in `patricia-bench.md`
confirm constant-sized allocation for disjoint native unions and substantially
less allocation for the overlapping workload.  This restores the intended
operational behavior, but it is benchmark evidence rather than a complexity
proof.

The remaining native-refinement task is the exception-based string `set` and
the target-level `==` contract for the specialized native unions.
`SPECIFICATION.md` states that contract precisely: a successful physical test
denotes the same current immutable tree and therefore equal lookups. A cost
semantics is additionally needed before making a formal asymptotic claim. This
is intentionally a runtime/compiler contract rather than a portable OCaml
theorem: documented `==` behavior on non-mutable values guarantees only
`compare = 0`, which is insufficient for arbitrary map payloads.

### 2. The direct-string biased unions are verified

The string proofs cover the bit view, first-difference scan, lookup/elements
agreement, removal, mapping, general `set`, generic `combine`, and both biased
unions, including fresh-key insertion and every branch-prefix relationship.

The general `set_correct_wf` theorem establishes well-formedness and the
pointwise lookup law for both fresh and existing keys, and
`replace_binding_correct_wf` derives the update-or-remove law. The public fuel
bound is proved sufficient for all recursive shapes,
`combine_fuel_correct_wf` proves the generic pointwise lookup law and
well-formedness simultaneously, and
`join_separated_correct_wf` establishes the left-biased join law for explicitly
separated well-formed trees, including empty filtered sides. Randomized merge
testing remains supporting evidence for the separately extracted native
implementation.

`union_left_correct_wf` and `union_right_correct_wf` specialize the generic
combine law, preserving well-formedness and selecting the preferred binding at
every key. `beq_correct_wf` gives the pointwise Boolean equality law, while
`beq_extensional_wf` proves equivalence to identical lookup results when the
value comparison reflects equality. Both variants package lookup equality as
`equiv`, prove its equivalence-relation laws, and prove
`equiv_elements_wf`: on well-formed trees it holds exactly when every binding
has the same membership in both `elements` lists. `wf_elements_bit_lex_sorted`
proves that
the key projection of `elements` is strongly sorted by the first differing
prefix-free logical bit, with `false` before `true`; thus every earlier key is
related to every later key, not merely to its immediate successor.

### 3. The raw extracted backend exposes values outside the proof contract

Separate extraction exposes the tree constructors and internal dependencies,
including `branch`, `join`, `insert_at`, `replace_binding`, and
`combine_fuel`. OCaml clients can therefore:

- construct a branch that violates the routing invariant;
- call `combine_fuel` with insufficient fuel;
- pass zero or negative integers to an API proved over Rocq `positive` keys;
- pass a combining function that violates `f None None = None` and then expect
  the finite-map lookup theorem.

The generated types do not enforce the proof boundary and are therefore named
`PatriciaInternal` and `StringPatriciaInternal` by the build. Supported clients
instead compile against handwritten `PatriciaMap.mli` and
`StringPatriciaMap.mli` interfaces. Their map types are abstract and their
operation set excludes constructors, representatives, branch/join helpers,
change workers, low-level bit operations, packed split tokens, and combine
workers. The structural oracle retains deliberate access to the internal
modules; the benchmark exercises the wrappers.

`PatriciaMap.Key.t` is also abstract. Its only public constructors validate a
native integer and reject every value below one, while `to_int` permits explicit
conversion back to the representation. Thus supported clients cannot supply a
zero or negative key. This enforces the input side of the current
`1 .. max_int` extraction domain; proving the finite-width refinement remains a
separate task.

The supported `combine` no longer accepts the raw two-option callback. Instead,
its `combiner` record separates the only three cases in which a binding can
exist: `left_only`, `right_only`, and `both`. The wrapper maps the fourth raw
case, absence from both inputs, directly to `None`. Consequently a supported
client cannot violate the theorem's `f None None = None` premise. The raw
callback remains available only in the explicitly internal modules used for
differential and structural validation.

### 4. Custom extraction constants are a trusted correctness boundary

The Rocq model uses unbounded `positive`, `N`, and `nat`, while the optimized
OCaml implementation uses bounded `int`, native shifts, and native strings.
`bit_at`, `first_diff`, prefix matching, routing bits, highest-differing-bit
selection, cached representatives, and fused string insertion are replaced
with handwritten OCaml realizers. Both general `combine` definitions and both
public biased unions are now extracted from proved structural source workers.
Rocq does not prove the equivalence of the remaining replacements.

This is not merely a general warning about extraction. The
[Rocq extraction manual](https://rocq-prover.org/doc/master/refman/addendum/extraction.html)
states that realizing strings are copied into generated files and that their
correctness is the user's responsibility. The imported
[`ExtrOcamlNatInt`](https://rocq-prover.org/doc/master/stdlib/Stdlib.extraction.ExtrOcamlNatInt.html)
and
[`ExtrOcamlZInt`](https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.extraction.ExtrOcamlZInt.html)
modules likewise describe their native arithmetic realizers as uncertified and
warn about overflow. Successful `Print Assumptions` output for a source theorem
does not inspect either kind of extraction directive.

#### Deviation-by-deviation audit

| Native deviation | What present validation establishes | Formal status and proof route |
| --- | --- | --- |
| `positive`, `N`, and `nat` represented by OCaml `int`; Rocq strings represented by OCaml strings | Wrapper tests reject `min_int`, negative values, and zero; accept and round-trip one and `max_int`; and the oracle covers positive keys through `max_int`, byte strings, and valid split positions used by the map | `NativeRefinement.v` fixes the supported 64-bit non-negative `int` payload domain at 62 bits and names the positive-key relation. Its integer routing model now has kernel-checked correspondence and closure laws. The link from that model to OCaml arithmetic and the bounded string representation remains a foreign-interface refinement obligation. |
| Integer `word`, prefix, prefix match, routing bit, highest differing bit, and mask ordering | Boundary-key fuzzing and structural checks found no mismatch | `native_prefix_word_refines`, `native_matches_prefix_refines`, `native_zero_bit_refines`, `native_highest_differing_bit_refines`, and `native_mask_above_refines` identify the bounded source model with the pure operations. The 62-bit payload/mask closure lemmas cover shifted prefixes and XOR-derived split bits. The custom OCaml `lsr`/`land`/`lxor`/loop realization is still trusted until a target-language primitive contract proves it implements this model. |
| Packed string split token `(byte << 4) | tag`, native `bit_at`, and bytewise `first_diff` | `first_diff` is checked for all 65,536 one-byte pairs plus prefix and long-prefix cases; direct checks cover all 16 tags at in-range and out-of-range byte indices, and structural tests check `bit_at` routing over NUL, non-ASCII, and randomized strings | `NativeRefinement.v` proves the logical `9*b+t` to packed `16*b+t` codec, valid-tag property, injectivity, ordering, and valid-token decode/encode round trips. Its native byte-code-array model proves byte length/access/bounds, the guard conditions for every `unsafe_get` site, and `native_packed_bit_at_refines_representation`; its safe structural bytewise scanner is proved equal to packed `first_diff`, and its mismatching-byte choice is equivalent to the Boolean-XOR leading-zeroes model. The remaining FFI contract is only that OCaml byte strings implement this array model, `String.length`/`Char.code` return the stated length/code, and short-circuit guards precede each unsafe access; OCaml execution itself is not kernel-verified. Logical position 9 remains token 16, so direct equality at the same extracted integer is intentionally false. |
| A branch sample returned as its constant-time `representative` | `wf_branch` requires `resident sample (Branch ...)`, and every smart constructor and public-operation preservation theorem discharges that premise; structural tests independently check the property | Cached-sample residency is kernel-checked (`wf_cached_sample_resident`). The cached and pure representatives can differ, but `wf_cached_sample_same_prefix_representative` proves agreement below the branch split. `wf_cached_sample_agrees_before_representative` and `wf_cached_sample_bit_at_before_representative` therefore justify every bounded-prefix comparison and strictly-outer routing-bit use in native merge/union without requiring representative equality. |
| Exception-based one-descent string `set` | Existing/fresh-key oracle tests and structural checks pass; its ordinarily extracted source worker is checked in the randomized oracle | The source-level `set_descend`/`set_one_descent` worker is proved equal to `set` on well-formed inputs. A 10K native trial allocated substantially more for the extracted worker (fixed-width build 993,458 vs. 726,896 words; updates 1,578,027 vs. 923,171), so the supported wrapper retains the exception realizer. Prove that exact realization in a target-language logic, or improve the extracted worker before replacing it. |
| Fuel-free integer and string `combine` | The public source workers use nested structural fixpoints and are proved equal to every sufficient `combine_fuel` run; the optimized extraction now retains those definitions, and randomized native merges agree with the reference maps | No Patricia-specific `Extract Constant` remains for general `combine`; ordinary extraction/compiler correctness and the retained primitive mappings remain in the trusted base. |
| Specialized biased unions and physical-identity (`==`) sharing | Disjoint and overlap results agree with `Stdlib.Map`; both public wrappers use the handwritten native realization. The closure-free fuel worker is proved equal to the established changed worker and is the source-level functional oracle; the isolated workers have invariant and pointwise union proofs plus a targeted extraction oracle. The checked `union-profile` reports the native realization's fixed allocation and left-root reuse for subset/equal/no-op inputs. Both `union_left_native_correct_wf` theorems assemble all reuse branches into a whole-worker invariant and pointwise union law conditional on `native_same_sound`; the direct-string theorem retains cached-sample residency. | The handwritten realization's `==` branch-reuse decisions are still trusted. A target-language/heap refinement must establish `native_same_sound` for OCaml `==`. Any physical-sharing/allocation claim additionally needs a cost or heap semantics. |

The packed-token and cached-representative rows are the most important subtle
cases. They are representation refinements, not pointwise replacements of the
same source values. A differential test of public maps can validate their
composition while still missing a bad direct call to the separately exported
`StringBits.bit_at` or `StringPatricia.representative`.

The current documentation states this honestly, and the extra fuzzing found no
mismatch. Nevertheless, an implementation using unproved `Extract Constant`
refinements cannot be described as end-to-end formally verified.

There are three defensible completion choices:

1. **Proof-aligned baseline:** retain ordinary extraction of the pure Rocq
   definitions. This removes the handwritten algorithm substitutions and is a
   useful differential oracle, but ordinary extraction and `ocamlopt` still
   remain in the trusted computing base.
2. **Source-level native model:** use Rocq's specified 63-bit integers and
   primitive byte strings, prove the optimized algorithms over those types, and
   extract the proved definitions. Rocq documents these primitives and their
   OCaml mappings, although their primitive implementations remain explicit
   trusted axioms in `Print Assumptions`; see the
   [primitive-object documentation](https://rocq-prover.org/doc/V9.2.0/refman/language/core/primitive.html).
3. **Verified native refinement:** introduce an explicit finite-width word and
   byte-string model, prove refinement lemmas for every native operation, and
   connect the OCaml primitives to that model through a separately audited or
   verified foreign-function boundary.

Keeping both backends is useful: the proof-aligned backend can serve as an
executable reference oracle for differential tests of the optimized backend.
For a stronger compilation story, external primitives need formal
specifications and a verified or explicitly trusted compilation boundary.

#### Can the current deviations be formally proved?

Yes for their functional behavior, but not by attaching a proof to the current
`Extract Constant` strings. The practical route is:

1. define each optimized algorithm and finite representation in Rocq;
2. prove a refinement theorem to the existing pure map specification;
3. extract that proved definition, leaving only a small primitive interface;
4. give that interface a formal target-language specification or accept it as
   an explicitly enumerated trusted boundary.

The bounded prefix scanner, direct merge, specialized union, first-difference
scanner, cached representative, and one-descent fused `set` worker now have
the relevant source-level specifications or refinement proofs. Their packed,
physical-sharing, and exception-based target realizations still depend on the
documented foreign-interface contracts. Exact claims about OCaml
exceptions, `String.unsafe_get`, physical equality, allocation, and generated
machine code require an OCaml/Clight semantics and a verified compiler or a
separate deductive verification of the target code. Testing can reduce risk but
cannot turn those target constructs into kernel-checked theorems.

### 5. Repository tests now exercise the extraction-refinement boundary

The deterministic randomized harness now exercises integer keys at every
native bit boundary through `max_int`, and it checks elements, branch routing,
non-empty children, and mask order. Its string counterpart generates byte
strings in addition to targeted empty, NUL, prefix, non-ASCII, and long-prefix
cases; it validates elements, split order, sample membership, routing, both
biased unions, and combining functions that delete one-sided or overlapping
bindings.

`PatriciaReferenceExtract.v` now retains a second executable backend generated
from the Rocq definitions without any Patricia-specific `Extract Constant`
realizers. The build packs its generated modules under `PatriciaReference`, so
the regular test target can link them beside the optimized modules without
name collisions. Deterministic differential workloads compare bindings,
lookups, membership, updates, removals, mapping/filtering, general combine,
both biased unions, folds, and equality for integer and arbitrary-byte string
keys. Low-level checks translate between logical string-bit positions and the
optimized packed tokens before comparing `bit_at`, `first_diff`, and both
prefix-agreement functions.

The standard native integer/string extraction mappings are shared by both
backends and remain trusted. Passing differential tests is supporting evidence
against errors in the handwritten Patricia optimizations; it is not a formal
refinement theorem or a verification of the extraction pipeline. Repository CI
wiring also remains to be added. Merge timing and allocation benchmarks exist
in `patricia-bench.md`.

### 6. The public maps are not yet `Map.Make`-compatible; ordered API and sets are a separate completion track

This repository uses OCaml 4.14.3 in its build configuration.  Its
`Map.Make` result implements the 40-value `Map.S` signature (in addition to
the `key` and covariant map-type declarations).  `PatriciaMap` and
`StringPatriciaMap` deliberately expose a smaller, safer API instead: they
have `empty`, `is_empty`, `singleton`, `get`, `mem`, `set`, `remove`, a
key-aware `map`, `map_filter`, restricted `combine`, two biased unions,
`elements`, a state-first `fold`, and `beq`.

They therefore do **not** currently implement `Map.S`, and cannot simply be
ascribed that signature.  The following is an API audit, not just a list of
renamings:

| `Map.S` group | Current status | Required compatibility work |
| --- | --- | --- |
| `empty`, `is_empty`, `mem`, `singleton`, `remove` | Present with the same observable meaning | Retain and prove/expose the usual `Map.S` laws.  The documented physical-identity clauses remain outside the current proof claim. |
| `add`, `find_opt`, `find`, `update` | `set` is `add` semantically and `get` is `find_opt`; no `find` or `update` | Add aliases/wrappers.  `update k f` is `replace_binding k (f (get k m)) m`; prove its pointwise law and use an OCaml wrapper only for `Not_found` in `find`. |
| `merge`, `union` | `combine` is a safe three-case, key-less combination; `union_left`/`union_right` are fixed biases | Add standard `merge` and conflict-only `union`.  `merge` can adapt its key-aware callback to the three represented cases, with absent/absent fixed to `None`; its usual lookup theorem still has the standard premise `f k None None = None`.  Keep the current restricted `combine` and biased unions as useful extra operations. |
| `equal`, `compare` | `beq` has the semantic role of `equal`; no lexicographic `compare` | Export `equal = beq` under the compatibility name and define `compare` over sorted bindings using `Key.compare`/`String.compare` and the supplied value comparator. |
| `iter`, `fold`, `for_all`, `exists` | Only a state-first, key-aware `fold` and internal `forallb` exist | Add the standard argument order and traversal functions.  The existing fold must be renamed or retained only as a non-`Map.S` extra: its type is incompatible with `Map.S.fold`. |
| `filter`, `filter_map`, `partition` | `map_filter` is the semantic core of `filter_map` | Export `filter` and `filter_map`; derive/prove `partition`, preferably with one paired traversal rather than two passes. |
| `cardinal`, `bindings`, extrema, `choose`, `split` | Absent; `elements` is close to `bindings` | Add them only after proving `elements` is ordered by the public key comparison.  `split` can first be specified/implemented through filtering; a Patricia-specific logarithmic split is a later optimization. |
| `find_first[_opt]`, `find_last[_opt]` | Absent | Scan ordered bindings initially and prove the least/greatest result under the documented monotonicity premise. |
| `map`, `mapi` | Current `map` is key-aware, hence has `mapi` semantics | This is a source-incompatible name collision.  A `Map.S` module must call the existing operation `mapi` and provide value-only `map`.  In addition, callback order must be made explicitly increasing; structural extraction alone does not provide that OCaml evaluation-order guarantee. |
| `to_seq`, `to_rev_seq`, `to_seq_from`, `add_seq`, `of_seq` | Absent | Add wrappers over proved ordered bindings (and document whether the first implementation eagerly materializes the binding list). |

The order requirement is the material blocker, rather than the missing
wrappers.  The positive-key proofs establish uniqueness and
lookup/elements agreement, but do not yet state that `elements` is increasing
under `Pos.compare`.  The string proofs establish
`wf_elements_bit_lex_sorted`, but do not yet connect `bit_lex_lt` to the
public `String.compare` order.  The latter connection should show that the
continuation-marker/most-significant-bit encoding orders bytes lexicographically
and puts a proper prefix first.  Until these two bridge theorems exist, it is
unsound to advertise `elements` as `bindings`, or to implement extrema,
`split`, ordered iteration, comparison, or first/last search with the
standard-library contracts.  The native comparison of arbitrary OCaml byte
strings also belongs in the already documented extraction-refinement boundary.

There are two viable API designs:

1. Make a major-version change to the existing public wrappers: rename the
   current key-aware `map` to `mapi`, `map_filter` to `filter_map`, and the
   current fold to a clearly nonstandard name; then implement the `Map.S`
   names and expose `type +'a t`.
2. Preserve the present API and add separate `PatriciaMapStdlib` and
   `StringPatriciaMapStdlib` modules which satisfy `Map.S` while retaining the
   current wrappers as the proof-oriented API.

The second route avoids breaking clients and is preferable unless source
compatibility is explicitly unimportant.  Neither route makes these modules
themselves `Map.Make`: they are fixed-key implementations.  A genuinely
generic Patricia `Make` functor would require a Rocq key/bit-decomposition
interface and proofs of its prefix, first-difference, routing, and ordering
laws; that is a substantially different generalization.

Sets should be added as two further abstract wrappers,
`PatriciaSet` and `StringPatriciaSet`, not as a new tree representation.  An
implementation may use `unit PatriciaMap.t` internally, but must keep that
representation abstract.  This reuses compression, lookup, deletion, and
merge while yielding the complete `Set.S` surface: membership/update,
`union`, `inter`, `disjoint`, `diff`, subset/equality/comparison, ordered
traversal and transformations, partition/cardinality/extrema/split/search,
and the sequence/list constructors.  In particular, set `map` and
`filter_map` must insert their output keys, because different input elements
can map to the same output element.

The proof cost for basic set operations is modest once the map API laws are
available.  Define `member key s := get key s = Some tt` and a set
extensionality relation, then derive:

```coq
member key (union left right) <-> member key left \/ member key right.
member key (inter left right) <-> member key left /\ member key right.
member key (diff left right)  <-> member key left /\ ~ member key right.
member key (map f set)       <-> exists x, member x set /\ f x = key.
```

`wf` preservation follows from the corresponding map `set`, `map_filter`,
and `combine` theorems.  The image theorem for set `map`/`filter_map`, and
the ordered `elements`/comparison/extrema theorems, are new proof obligations;
they are not consequences of pointwise map lookup alone.  The same ordered
bridge theorems are therefore prerequisites for both full `Map.S` support and
full `Set.S` support.

An initial compatibility implementation may build `partition`, `split`,
set intersection/difference, and sequence operations from `map_filter`,
`fold`, and ordered bindings.  It will be functionally correct but can be
linear or worse and may lose physical sharing.  Fast versions should be
introduced as source-level Patricia workers and proved as refinements before
adding native realizers.  In particular, the physical-equality guarantees in
the standard interfaces must either be implemented with a `changed` result
and separately justified, or explicitly excluded from the verified claim;
semantic `Map.S`/`Set.S` compatibility alone does not establish them.

## Plan and completion tracking

Open decisions, prioritized work, completed foundations, validation commands,
and completion gates are tracked in
[`patricia-todo.md`](patricia-todo.md). This review intentionally records the
current evidence and verification boundary only; it is not a second task list.
