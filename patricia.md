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
| Extracted native OCaml | Extensive oracle and invariant testing passes, but the standard numeric/string mappings and 19 explicit handwritten realizers are trusted; neither their refinement nor the Rocq-to-OCaml compilation pipeline is proved here |

Consequently, “formally verified” is accurate for the stated theorems about the
pure definitions. It is not yet accurate as an end-to-end claim about the
optimized OCaml library.

## Validation results

The following checks passed:

- `make -C patricia`, including all Rocq proof files, extraction, OCaml
  compilation, and the deterministic randomized oracle test;
- a source scan found no `Admitted`, `admit`, `Axiom`, aborted proof, or similar
  unresolved proof escape in the Patricia sources;
- `Print Assumptions` reported the inspected integer `combine_correct_wf` and
  string `set_correct_wf`, `replace_binding_correct_wf`,
  `join_separated_correct_wf`, `public_combine_fuel_sufficient`,
  `union_left_correct_wf`, `union_right_correct_wf`, `beq_correct_wf`,
  both variants' `equiv_elements_wf` and `beq_extensional_wf`, plus string
  `wf_elements_bit_lex_sorted` and `wf_splits_ordered`, as closed under the
  global context;
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

### 3. The extracted interface exposes values outside the proof contract

Separate extraction exposes the tree constructors and internal dependencies,
including `branch`, `join`, `insert_at`, `replace_binding`, and
`combine_fuel`. OCaml clients can therefore:

- construct a branch that violates the routing invariant;
- call `combine_fuel` with insufficient fuel;
- pass zero or negative integers to an API proved over Rocq `positive` keys;
- pass a combining function that violates `f None None = None` and then expect
  the finite-map lookup theorem.

The README documents part of this boundary, but the generated types do not
enforce it. Complete library verification requires an abstract public type and
an interface that makes malformed trees unrepresentable to clients.

Recommended correction:

- add a handwritten wrapper `.mli` with abstract map types;
- expose only proved smart constructors and operations;
- hide fuel, branch construction, representatives, and proof-internal merge
  helpers;
- use an abstract validated positive key type, or explicitly choose and verify
  a different native integer key domain;
- document `combine`'s finite-map condition in the public API, and provide
  common combinators whose condition is proved once.

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
| `positive`, `N`, and `nat` represented by OCaml `int`; Rocq strings represented by OCaml strings | Tests cover positive keys through `max_int`, byte strings, and valid split positions used by the map | Source theorems use unbounded values. State a fixed-width key/string representation relation and prove every operation within it, or change the source model to `Uint63` and primitive strings. Inputs outside the relation must be rejected by the wrapper. |
| Integer `word`, prefix, prefix match, routing bit, highest differing bit, and mask ordering | Boundary-key fuzzing and structural checks found no mismatch | These are small, formally provable word lemmas. Prove them against a 63-bit model; equality with the unbounded model then holds for keys in `1 .. max_int`. |
| Packed string split token `(byte << 4) | tag`, native `bit_at`, and bytewise `first_diff` | `first_diff` is checked for all 65,536 one-byte pairs plus prefix and long-prefix cases; structural tests check `bit_at` routing over NUL, non-ASCII, and randomized strings | This requires a relational theorem, not equality at the same extracted integer: logical position 9 is encoded as token 16, and exported native `bit_at s 9` therefore does not denote pure `bit_at s 9`. Prove `native_bit_at s (encode n) = bit_at s n`, `native_first_diff = option_map encode first_diff`, validity and order preservation of tokens, then hide raw tokens from clients. |
| A branch sample returned as its constant-time `representative` | Structural tests check that samples in public-operation results are resident keys | Existing `wf` only constrains the sample's prefix; it does not say the sample is resident. Strengthen the invariant with sample residency and prove every constructor preserves it, or keep the source representative descent. Without that stronger invariant, this realizer is not equivalent even on every currently `wf` tree. |
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
For a stronger compilation story, CertiCoq targets CompCert Clight, and the
2025 [verified Coq/C FFI work](https://doi.org/10.1145/3704860) shows how
external primitives can receive formal specifications. This is a possible
architecture, not a drop-in completion: the
[CertiCoq project](https://certicoq.org/) still describes parts of its compiler
verification as work in progress.

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

### 5. Repository tests now cover functional boundaries, but not extraction refinement

The deterministic randomized harness now exercises integer keys at every
native bit boundary through `max_int`, and it checks elements, branch routing,
non-empty children, and mask order. Its string counterpart generates byte
strings in addition to targeted empty, NUL, prefix, non-ASCII, and long-prefix
cases; it validates elements, split order, sample membership, routing, both
biased unions, and combining functions that delete one-sided or overlapping
bindings.

Still missing are a differential test against a proof-aligned extracted
reference, direct contract tests for separately exported low-level functions,
and CI wiring. Merge timing and allocation benchmarks now exist in
`patricia-bench.md`. All tests remain supporting evidence only; they do not
validate the custom extraction constants formally.

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
- [ ] the cached string branch sample is a resident binding; this stronger
  invariant is required by the native constant-time `representative` realizer;
- [x] keys and bindings in `elements` are unique on well-formed trees;
- [x] direct-string `elements` is strongly sorted by prefix-free bit-stream
  lexicographic order (`wf_elements_bit_lex_sorted`);
- [x] lookup is extensionally equivalent to membership in `elements` on
  well-formed trees;
- [ ] every value constructed through the public API is well formed; string
  `join` and merge are still missing preservation proofs.

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

### Phase 5: close the complete API laws

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
- [ ] Any laws required by the intended CompCert `TREE` adapter.

If structural equality of canonical trees is desired, prove that separately;
finite-map extensional equality is sufficient for most clients.

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

- [ ] Generate an internal module and place an abstract handwritten wrapper around
  it.
- [ ] Add checked conversions for native integer keys.
- [ ] Prevent clients from constructing malformed values or supplying fuel.
- [ ] Hide packed split tokens and low-level bit functions, or expose wrapper
  functions that encode and decode logical positions.
- [ ] Add a CompCert `TREE` adapter only after its required laws are enumerated and
  proved.
- [x] Make extraction reproducible through the normal build and ensure generated
  files are never hand-edited.
- [ ] Run `Print Assumptions` over every exported correctness theorem in CI, not
  only selected examples.

### Phase 8: expand automated validation

Current validation status:

- [x] Integer keys around every bit boundary and near `max_int`;
- [x] Arbitrary byte strings, empty strings, embedded NULs, prefix-related keys,
  non-ASCII bytes, and long common prefixes;
- [x] Fresh and existing insertion, absent and present removal, and repeated
  collapse of branches;
- [ ] All merge shapes: equal roots, left containment, right containment, and
  disjoint prefixes;
- [x] Combining functions that preserve, transform, or delete left-only,
  right-only, and overlapping bindings;
- [x] Both specialized unions;
- [x] `elements` completeness, uniqueness, and documented order, including
  byte-lexicographic randomized checks for direct strings;
- [x] Structural well-formedness of every tested result;
- [ ] Differential equivalence between pure and optimized extraction backends.

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
