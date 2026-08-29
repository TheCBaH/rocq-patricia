# Patricia-tree review and formal-verification roadmap

Review date: 2026-08-28

## Scope and verdict

The review covers the standalone implementation under `patricia/`: the
positive-integer Patricia tree, the direct byte-string Patricia tree, their
Rocq proofs, OCaml extraction directives, and the randomized OCaml test
harness.

The implementation is a strong executable and proof-development sketch. The
positive-key implementation has substantial functional-correctness coverage,
and both extracted implementations behaved correctly in the supplied tests
and in additional fuzzing. It is not yet a complete formally verified
mergeable-map library, however. The direct-string implementation is missing
merge proofs, the extracted API does not enforce the proved preconditions, and
the runtime fuel calculation defeats the intended fast-disjoint-merge behavior.

## Validation results

The following checks passed:

- `make -C patricia`, including all Rocq proof files, extraction, OCaml
  compilation, and the deterministic randomized oracle test;
- a source scan found no `Admitted`, `admit`, `Axiom`, aborted proof, or similar
  unresolved proof escape in the Patricia sources;
- `Print Assumptions` reported the inspected integer `combine_correct_wf` and
  string `set_correct_wf`, `replace_binding_correct_wf`, and
  `join_separated_correct_wf`, `public_combine_fuel_sufficient`, and
  `wf_splits_ordered` theorems as closed under the global context;
- additional integer fuzzing used keys across the positive OCaml `int` range,
  including high-bit boundary values, and checked lookup, elements, merge, and
  routing invariants;
- additional string fuzzing used arbitrary byte strings, including non-ASCII
  bytes, and checked lookup, elements, merge, branch separation, prefix
  agreement, non-empty children, and increasing split positions.

No functional counterexample was found by these checks. Fuzzing is supporting
evidence only; it does not close the proof gaps described below.

## Review findings

### 1. Runtime fuel defeats fast merge

Both public `combine` definitions calculate fuel with
`S (size left + size right)`. Computing `size` traverses every node before the
merge begins. Consequently, even a merge of immediately disjoint trees has
linear work in the combined tree size.

The disjoint cases additionally call `map_left` and `map_right`. These
functions rebuild every retained node. In particular, `union_left` and
`union_right` are defined through generic `combine`, so they do not reuse
unchanged disjoint subtrees even though their one-sided mapping functions are
identities.

This does not invalidate the lookup theorems, but it defeats the main
performance property expected from an Okasaki--Gill-style mergeable Patricia
tree.

Recommended correction:

1. Define merge using well-founded recursion whose termination evidence lives
   in `Prop` and is erased during extraction. Avoid computing whole-tree fuel
   at runtime.
2. Separate generic combining, which may genuinely need to transform every
   one-sided binding, from specialized biased union.
3. Give biased union an implementation that returns unchanged disjoint
   subtrees directly.
4. Add a cost semantics if asymptotic behavior is to be a formally verified
   claim. At minimum, benchmark disjoint and overlapping inputs and inspect
   allocation behavior in extracted OCaml.

### 2. The direct-string core is only partially verified

The string proofs cover the bit view, first-difference scan, lookup/elements
agreement, removal, mapping, and general `set`, including fresh-key insertion.
They do not yet establish the general laws for:

- `combine_fuel` and public `combine`;
- the specialized string unions.

The general `set_correct_wf` theorem establishes well-formedness and the
pointwise lookup law for both fresh and existing keys, and
`replace_binding_correct_wf` derives the update-or-remove law. The public
fuel bound is proved sufficient for all recursive shapes, while
`join_separated_correct_wf` establishes the left-biased join law for explicitly
separated well-formed trees, including empty filtered sides. Randomized merge
success still does not establish the general merge specification.

This is the largest functional-verification gap.

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
`bit_at`, `first_diff`, prefix matching, routing bits, and highest-differing-bit
selection are replaced with handwritten OCaml realizers. Rocq proves the pure
definitions, not the equivalence of these replacements.

The current documentation states this honestly, and the extra fuzzing found no
mismatch. Nevertheless, an implementation using unproved `Extract Constant`
refinements cannot be described as end-to-end formally verified.

There are two defensible completion choices:

1. **Verified baseline:** retain standard extraction of the pure Rocq
   definitions. This minimizes the trusted boundary but may be slower.
2. **Verified native refinement:** introduce an explicit finite-width word and
   byte-string model, prove refinement lemmas for every native operation, and
   connect the OCaml primitives to that model through a separately audited or
   verified foreign-function boundary.

Keeping both backends is useful: the pure backend can serve as an executable
reference oracle for differential tests of the optimized backend.

### 5. Repository tests now cover functional boundaries, but not extraction refinement

The deterministic randomized harness now exercises integer keys at every
native bit boundary through `max_int`, and it checks elements, branch routing,
non-empty children, and mask order. Its string counterpart generates byte
strings in addition to targeted empty, NUL, prefix, non-ASCII, and long-prefix
cases; it validates elements, split order, sample membership, routing, both
biased unions, and combining functions that delete one-sided or overlapping
bindings.

Still missing are a differential test against a pure extracted reference,
benchmarks/allocation checks for merge behavior, and CI wiring. The tests are
supporting evidence only and do not validate the custom extraction constants.

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
- [x] representatives are actual bindings (`representative_elements`);
- [x] keys and bindings in `elements` are unique on well-formed trees;
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

1. [ ] Prove representative and prefix-agreement lemmas for equal-split,
   containment, and disjoint-prefix cases;
2. [x] Define and prove sufficiency of the recursive-call fuel measure;
3. [ ] Prove `combine_fuel` correctness and well-formedness simultaneously;
4. [ ] Lift the result to public `combine` under `f None None = None`;
5. [ ] Derive left- and right-biased union laws.

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
- [ ] `combine` and specialized union laws: complete for positive keys, open
  for direct strings;
- [ ] Extensional equality and a `beq` correctness theorem: complete for
  positive keys, open for direct strings;
- [ ] The documented `elements` ordering, not only uniqueness: tested for
  positive keys but not established for direct strings;
- [x] Fold equivalence to the traversal order produced by `elements`;
- [ ] An extensionality theorem saying equal lookup at every key represents the
  same finite map;
- [ ] Any laws required by the intended CompCert `TREE` adapter.

If structural equality of canonical trees is desired, prove that separately;
finite-map extensional equality is sufficient for most clients.

### Phase 6: remove runtime fuel from the optimized implementation

Status: no items in this phase are complete. Both current public `combine`
definitions still evaluate a whole-tree `size` fuel bound before merging.

Use well-founded recursion over a lexicographic or combined structural measure
and keep the accessibility proof in `Prop`, so extraction removes it. Verify
the extracted code to ensure it does not compute `size` before merging.

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
- [ ] `elements` completeness, uniqueness, and documented order: completeness
  and uniqueness are checked, but direct-string ordering is not documented;
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
   pure verified backend retained.
6. No runtime whole-tree fuel calculation defeats the promised fast merge.
7. All exported theorems pass assumption auditing, all extraction targets
   build reproducibly, and the expanded oracle and invariant tests pass in CI.
8. Any complexity claim is backed by an explicit cost theorem; otherwise the
   documentation limits itself to functional correctness plus benchmark
   evidence.
