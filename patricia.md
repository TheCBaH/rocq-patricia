# Patricia-tree review and formal-verification roadmap

Review date: 2026-08-29

## Scope and verdict

The review covers the standalone implementation under `patricia/`: the
positive-integer Patricia tree, the direct byte-string Patricia tree, their
Rocq proofs, OCaml extraction directives, and the randomized OCaml test
harness.

The implementation is a strong executable and proof-development sketch. The
positive-key source model has substantial functional-correctness coverage, and
both extracted implementations behaved correctly in the supplied tests and in
additional fuzzing. It is not yet a complete formally verified mergeable-map
library, however. The extracted API does not enforce the proved preconditions,
and the optimized native extraction is a second implementation rather than a
proved compilation of the Rocq definitions.

The verification claim must therefore be split into three layers:

| Layer | Current status |
| --- | --- |
| Pure positive-key Rocq model | Kernel-checked functional map laws, including general `combine` and finite-map extensionality, with no project axioms found in the inspected theorem closure |
| Pure direct-string Rocq model | Lookup, update, removal, ordered traversal, filtering, structural invariants, general `combine`, biased unions, and finite-map extensionality are proved |
| Extracted native OCaml | Extensive oracle, invariant, and optimized-versus-proof-aligned differential testing passes, but the standard numeric/string mappings and 19 explicit handwritten realizers are trusted; neither their refinement nor the Rocq-to-OCaml compilation pipeline is proved here |

Consequently, “formally verified” is accurate for the stated theorems about the
pure definitions. It is not yet accurate as an end-to-end claim about the
optimized OCaml library.

## Validation results

The following checks passed:

- `make -C patricia`, including all Rocq proof files, extraction, OCaml
  compilation, and the deterministic randomized oracle test;
- a source scan found no `Admitted`, `admit`, `Axiom`, aborted proof, or similar
  unresolved proof escape in the Patricia sources;
- the source-driven `Print Assumptions` audit discovers every top-level lemma,
  theorem, and corollary across the bit-specification, map-proof, and native
  representation modules, and reports each closed under the global context;
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

The Rocq definitions still calculate `S (size left + size right)` as fuel;
this makes their termination argument and existing proofs straightforward.
The native extraction now replaces `combine` with direct structural recursion,
so it does not compute that bound at runtime. Its leaf/tree cases delegate to
source-level workers with proved lookup and well-formedness laws, fusing an
overlapping replacement into the mapping pass. It also replaces `union_left`
with a specialized structural algorithm in both the integer and string
backends (`union_right` reverses its arguments).  Disjoint prefixes are joined
immediately, one-sided subtrees are reused, and only a changed recursive path
is rebuilt.

The 10,000- and 100,000-binding benchmark checks in `patricia-bench.md`
confirm constant-sized allocation for disjoint native unions and substantially
less allocation for the overlapping workload.  This restores the intended
operational behavior, but it is benchmark evidence rather than a complexity
proof.

The remaining verification task is to prove a well-founded version of this
algorithm or a refinement theorem connecting the direct extracted recursion
to the existing fuelled specification.  A cost semantics is additionally
needed before making a formal asymptotic claim.

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
selection, cached representatives, fused string insertion, direct `combine`,
and specialized biased union are replaced with handwritten OCaml realizers.
Rocq proves the pure definitions, not the equivalence of these replacements.

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
| `positive`, `N`, and `nat` represented by OCaml `int`; Rocq strings represented by OCaml strings | Wrapper tests reject `min_int`, negative values, and zero; accept and round-trip one and `max_int`; and the oracle covers positive keys through `max_int`, byte strings, and valid split positions used by the map | `NativeRefinement.v` fixes the supported 64-bit non-negative `int` payload domain at 62 bits and names the positive-key relation. It does not yet prove that native arithmetic, shifts, or the bounded string representation refine the unbounded source operations. |
| Integer `word`, prefix, prefix match, routing bit, highest differing bit, and mask ordering | Boundary-key fuzzing and structural checks found no mismatch | These are small, formally provable word lemmas. Prove them against the supported 62-bit non-negative OCaml-`int` payload model; equality with the unbounded model then holds for keys in `1 .. max_int`. |
| Packed string split token `(byte << 4) | tag`, native `bit_at`, and bytewise `first_diff` | `first_diff` is checked for all 65,536 one-byte pairs plus prefix and long-prefix cases; direct checks cover all 16 tags at in-range and out-of-range byte indices, and structural tests check `bit_at` routing over NUL, non-ASCII, and randomized strings | `NativeRefinement.v` proves the logical `9*b+t` to packed `16*b+t` codec, valid-tag property, injectivity, ordering, and valid-token decode/encode round trips. Its safe source-level packed `bit_at` worker follows the native byte/tag dispatch: tag 0 is true exactly for an in-range byte, and it is false for out-of-range bytes and tags 9–15. It is also proved correct at every encoded position. A safe structural bytewise scanner is proved equal to packed `first_diff`; its mismatching-byte choice is further proved equivalent to a Boolean-XOR leading-zeroes model. The native `Char.code`/integer-XOR and unsafe-byte-access realizers have not yet been proved to implement that model; logical position 9 remains token 16, so direct equality at the same extracted integer is intentionally false. |
| A branch sample returned as its constant-time `representative` | `wf_branch` now requires `resident sample (Branch ...)`, and every smart constructor and public-operation preservation theorem discharges that premise; structural tests independently check the property | Cached-sample residency is now kernel-checked (`wf_cached_sample_resident`). This justifies the native result as an actual binding, but it does not make it definitionally equal to the source representative, which may select a different resident key; consumers still require a refinement argument based on representative independence. |
| Exception-based one-descent string `set` | Existing/fresh-key oracle tests and structural checks pass | Define a source worker returning either a rebuilt tree or a discriminator to bubble upward, prove it equivalent to `set`, and extract it. Proving the exact local-exception OCaml code instead requires a target-language logic supporting exceptions. |
| Fuel-free integer and string `combine` | Randomized merges agree with reference maps; both source `combine` definitions are proved | Define well-founded recursion over `size left + size right`, prove its equations and equivalence to sufficiently fuelled `combine_fuel`, and extract that definition. |
| Specialized biased unions and physical-identity (`==`) sharing | Disjoint and overlap results agree with `Stdlib.Map`; allocation demonstrates sharing | Prove the semantic union law for a source-level specialized algorithm. Functional correctness does not prove physical sharing; a sharing/allocation claim needs a cost or heap semantics. A source worker can return a `changed` certificate to justify returning the original tree without relying on target physical equality. |

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

The bounded prefix scanner now has a source-level specification and equality
proof; its packed target realization still depends on the documented position
relation. The direct merge, specialized union, first-difference scanner,
cached representative, and fused set still need such source-level refinement
proofs. Exact claims about OCaml
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

## Roadmap to complete functional verification

### Phase 1: freeze the specification and trusted computing base

Before extending proofs, decide and record:

- whether the verified key domain is unbounded positive integers, all
  non-negative integers, or fixed-width unsigned words;
- whether native OCaml extraction is part of the verified claim or is an
  explicitly unverified optimized refinement;
- whether the string tree is a required public implementation or a separate
  experimental extension;
- the exact public operations, ordering of `elements`, semantics of `fold`,
  and precondition on `combine`;
- whether performance is tested, proved with a cost model, or intentionally
  excluded from the formal claim.

Write these decisions as a small module signature and a theorem checklist.
This prevents a proof of one representation from being mistaken for a proof
of a different extracted runtime representation.

### Phase 2: strengthen and package the invariants

For both tree variants, provide named results for all canonicality properties:

- [x] both branch children are non-empty, encoded in `wf_branch`;
- [x] every descendant key agrees with the branch prefix, encoded through
  `all_keys`/`same_prefix` in `wf_branch`;
- [x] the left and right subtrees have opposite routing bits;
- [x] descendant split positions are strictly ordered relative to ancestors
  (`wf_splits_ordered` for direct strings);
- [x] pure representatives are actual bindings (`representative_elements`);
- [x] the cached string branch sample is a resident binding
  (`wf_cached_sample_resident`), preserved by all proved smart operations;
- [x] keys and bindings in `elements` are unique on well-formed trees;
- [x] direct-string `elements` is strongly sorted by prefix-free bit-stream
  lexicographic order (`wf_elements_bit_lex_sorted`);
- [x] lookup is extensionally equivalent to membership in `elements` on
  well-formed trees;
- [x] every value constructed through the public API is well formed, including
  string `join`, generic combine, and both specialized unions.

The direct-string split-order consequence is now exposed as a named theorem,
so merge proofs can rely on it without reproving the contradiction between an
ancestor's routing bit and a descendant's branch partition.

If convenient, define a semantic finite-map relation such as:

```coq
represents m M := forall k, get k m = M k
```

and use it to separate functional-map laws from structural canonicality.

### Phase 3: fresh string insertion and disjoint join completed

Completed prerequisites and theorem:

1. [x] `first_diff fresh representative = Some split` gives prefix
   agreement below `split` and opposite bits at `split`.
2. [x] The singleton-fresh-side `branch_at` lookup and well-formedness laws
   needed by `insert_at` are proved.
3. [x] General `branch_at` correctness and well-formedness when its two
   input trees agree before `split` and occupy opposite sides.
4. [x] `join_disjoint_correct_wf` proves `join` correctness for distinct,
   compatible non-empty trees:

   ```coq
   wf (join fresh old) /\
   get k (join fresh old) =
     match get k fresh with Some v => Some v | None => get k old end
   ```

   under explicit prefix/bit separation hypotheses.

Completed: the routed-leaf `insert_at` invariant, fresh-key branch separation,
and the unconditional `set` law:

   ```coq
   wf m ->
   wf (set key value m) /\
   forall query,
     get query (set key value m) =
       if String.eqb query key then Some value else get query m.
   ```

### Phase 4: finish string filtering and merge

Completed: `map_filter` and its one-sided derivatives are proved. The next
merge dependency is to connect those laws to the structural prefix cases:

```coq
wf m ->
wf (map_filter f m) /\
forall k,
  get k (map_filter f m) =
    match get k m with None => None | Some v => f k v end.
```

The derived `map_left` and `map_right` laws carry the standard
`f None None = None` precondition. Completed:
`replace_binding_correct_wf` derives the update-or-remove law from the
unconditional `set` and `remove` theorems, and
`join_separated_correct_wf` covers the disjoint join case, including collapsed
filtered sides. Remaining work:

1. [x] Prove representative and prefix-agreement lemmas for equal-split,
   containment, and disjoint-prefix cases;
2. [x] Define and prove sufficiency of the recursive-call fuel measure;
3. [x] Prove `combine_fuel` correctness and well-formedness simultaneously;
4. [x] Lift the result to public `combine` under `f None None = None`;
5. [x] Derive left- and right-biased union laws.

The main final theorem should be:

```coq
f None None = None -> wf left -> wf right ->
wf (combine f left right) /\
forall key,
  get key (combine f left right) =
    f (get key left) (get key right).
```

### Phase 5: close the current custom API laws

Current API-law status across both key variants:

- [x] `empty`, `is_empty`, `singleton`, `get`, and `mem` laws;
- [x] Unconditional `set` and `remove` laws;
- [x] `map`, `map_filter`, `fold`, and `elements` laws;
- [x] `combine` and specialized union laws for both key variants;
- [x] Extensional equality and a `beq` correctness theorem for both key
  variants;
- [x] The documented `elements` ordering, including strong sorting for direct
  strings;
- [x] Fold equivalence to the traversal order produced by `elements`;
- [x] Extensionality theorems packaging equal lookup at every key as finite-map
  equivalence and characterizing it by binding membership;

If structural equality of canonical trees is desired, prove that separately;
finite-map extensional equality is sufficient for most clients.

This phase describes the present proof-oriented API, not the complete OCaml
`Map.S`/`Set.S` interfaces.  Before claiming standard-library compatibility,
complete the ordered traversal bridge theorems and the compatibility/set work
in finding 6: in particular, prove the public comparison order, callback
order, image laws for set transformations, and the semantics of every added
search, split, sequence, and exception-raising wrapper.

### Phase 6: remove runtime fuel from the optimized implementation

Status: the optimized extracted implementation is complete: its direct
`combine` does not evaluate a whole-tree size bound, and its specialized
biased union preserves disjoint and unchanged subtrees.  The proof-side
definition still uses fuel, so the formal refinement remains open.

Use well-founded recursion over a lexicographic or combined structural measure
and keep the accessibility proof in `Prop`, so extraction removes it. Prove it
extensionally equivalent to the fuelled definition, or verify the direct
native realization against that definition.

For generic `combine`, be precise about unavoidable work: an arbitrary
one-sided function may need to visit every retained binding. For biased union,
prove a specialized algorithm correct and verify that disjoint inputs reuse
existing subtrees. A formal complexity track can then define operation costs
and establish bounds for:

- lookup and update in terms of word width or key-bit length;
- disjoint biased union;
- overlapping merge in terms of the traversed spines and affected subtrees;
- allocation or constructor count if structural sharing is part of the claim.

### Phase 7: harden extraction and integration

- [x] Generate internal modules and place abstract handwritten wrappers around
  them.
- [x] Add checked conversions and an abstract public type for native integer keys.
- [x] Prevent supported clients from constructing malformed values or supplying fuel.
- [x] Hide packed split tokens and low-level bit functions, or expose wrapper
  functions that encode and decode logical positions.
- [x] Enforce the generic-combine finite-map condition through three explicit
  one-sided/overlap callbacks.
- [x] Specify the 62-bit native positive-key domain and the logical/packed
  string-position codec in Rocq, including a source-level packed `bit_at`
  worker and the canonical first-difference property needed by a bytewise
  scan.  The target arithmetic and bytewise-first-difference realizer
  refinement proofs remain open.
- [x] Make extraction reproducible through the normal build and ensure generated
  files are never hand-edited.
- [x] Run `Print Assumptions` over every top-level proof declaration during the
  normal build, with count checking so new declarations are included
  automatically. The audit includes `NativeRefinement.v`; repository-level CI
  wiring remains separate.

### Phase 8: expand automated validation

Current validation status:

- [x] Integer keys around every bit boundary and near `max_int`;
- [x] Arbitrary byte strings, empty strings, embedded NULs, prefix-related keys,
  non-ASCII bytes, and long common prefixes;
- [x] Fresh and existing insertion, absent and present removal, and repeated
  collapse of branches;
- [x] All merge shapes: equal roots, left containment, right containment, and
  disjoint prefixes, with deterministic dispatch classification in addition to
  randomized coverage;
- [x] Combining functions that preserve, transform, or delete left-only,
  right-only, and overlapping bindings;
- [x] Both specialized unions;
- [x] `elements` completeness, uniqueness, and documented order, including
  byte-lexicographic randomized checks for direct strings;
- [x] Structural well-formedness of every tested result;
- [x] Differential equivalence testing between proof-aligned and optimized
  extraction backends, including logical/packed string-position translation.

- [x] Add benchmarks that separately report runtime and allocation for disjoint
  and overlapping merges. `make -C patricia benchmark` compares extracted
  Patricia trees with `Stdlib.Map` for integer and 3-, 4-, and 5-character
  string keys, while validating each measured result. The recorded baseline
  and analysis are in `patricia-bench.md`; these are machine-specific
  measurements, not formal complexity proofs.

## Completion criteria

The project can reasonably claim complete functional verification when all of
the following hold:

1. Every public constructor and operation preserves the chosen invariant.
2. Every public operation has its pointwise finite-map specification proved.
3. String merge has the same proof coverage as the positive-key implementation.
4. The public extracted types prevent construction of values outside the proof
   contract.
5. The relationship between the proved model and native OCaml primitives is
   either itself verified or clearly excluded from the formal claim, with a
   proof-aligned reference backend retained.
6. No runtime whole-tree fuel calculation defeats the promised fast merge.
7. All exported theorems pass assumption auditing, all extraction targets
   build reproducibly, and the expanded oracle and invariant tests pass in CI.
8. Any complexity claim is backed by an explicit cost theorem; otherwise the
   documentation limits itself to functional correctness plus benchmark
   evidence.
9. If `Map.S` or `Set.S` compatibility is claimed, every operation in the
   selected OCaml-version signature is exported with its documented observable
   semantics, including increasing-order traversal and binding/element order;
   any physical-sharing guarantee is proved or explicitly excluded.
