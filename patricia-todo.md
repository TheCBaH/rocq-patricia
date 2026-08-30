# Patricia plan and tracker

Last updated: 2026-08-30

This document is the single source of truth for Patricia planning and progress.
The public contracts and trusted boundary are fixed in
[`SPECIFICATION.md`](SPECIFICATION.md), the supporting evidence is reviewed in
[`patricia.md`](patricia.md), and performance analysis and measurements are
recorded in [`patricia-str.md`](patricia-str.md) and
[`patricia-bench.md`](patricia-bench.md).

Checkboxes describe repository state: `[x]` is complete and validated, `[ ]`
is open, and `[-]` is intentionally deferred. When an item closes, add the
validation command and date to the tracking log.

## Current state

| Area | Status | Meaning |
| --- | --- | --- |
| Pure positive-key Rocq map | Complete for the current custom API | Public operations have functional laws and preserve the invariant |
| Pure direct-string Rocq map | Complete for the current custom API | Includes generic combine, biased unions, extensional equality, and bit-lexicographic element order |
| Supported OCaml wrappers | Hardened | Map representations and positive integer keys are abstract; malformed trees, raw fuel, packed tokens, and the absent/absent combine case are hidden |
| Optimized native extraction | Tested, not formally refined end to end | Oracle, invariant, and proof-aligned differential tests pass; custom realizers and native primitives remain trusted |
| `Map.S` / `Set.S` compatibility | Not claimed | Ordering bridges and most compatibility operations are not implemented |
| Repository CI | Configured | GitHub Actions runs `make` and a checked benchmark smoke workload; the first hosted run remains to be observed |
| Complexity guarantees | Not claimed | Benchmarks provide machine-specific evidence; there is no formal cost model |

The shortest defensible completion path is to freeze the claim at the current
pure-model boundary, automate it in CI, and explicitly retain optimized native
extraction as a tested trusted refinement. End-to-end native verification,
standard-library compatibility, and formal complexity are separate expansion
tracks.

## Decisions

These choices freeze the current scope. Do not broaden the verification claim
without revisiting the affected decision and recording the new claim in the
public specification.

- [x] **D1 — Verification claim:** claim kernel-checked functional correctness
  for the pure models and treat the optimized native backend as a tested,
  explicitly trusted refinement. End-to-end native refinement is not part of
  the current completion gate; choosing it later requires all of N1 and N2.
- [x] **D2 — Key and string domains:** retain unbounded Rocq `positive` and
  logical strings as the proved public model. Keep native `1 .. max_int` keys
  and OCaml byte strings as supported implementation domains behind an explicit
  refinement boundary. Do not migrate the proof development to fixed-width
  words or primitive byte strings merely to strengthen the extraction story.
- [x] **D3 — API scope:** freeze the current proof-oriented wrappers as the
  verified API. Standard-library compatibility is outside the current claim.
  If it is pursued later, add separate `PatriciaMapStdlib`,
  `StringPatriciaMapStdlib`, and set modules rather than breaking the current
  key-aware `map` and state-first `fold` API.
- [x] **D4 — Ordering contract:** defer standard-library compatibility, but fix
  its contract now: any future N3 modules use `Pos.compare` and OCaml
  `String.compare`, with increasing callback order as well as ordered result
  lists.
- [x] **D5 — Performance claim:** keep performance empirical. Benchmarks may
  support engineering comparisons and regression investigation, but no
  asymptotic, allocation, or physical-sharing guarantee is claimed unless N4
  first defines and connects an appropriate cost and heap semantics.

## Priority plan

### P0 — Freeze and automate the current claim

- [x] Resolve D1–D3. The selected scope matches the conservative verification
  boundary already stated in `README.md` and `patricia.md`.
- [x] Write a compact public specification and theorem checklist for both
  current wrappers: key domain, invariant boundary, operation semantics,
  `elements` order, `fold` order, and the enforced combine contract.
- [x] State the trusted computing base in that specification: Rocq kernel,
  extraction/compiler boundary, standard native mappings, and each custom
  realizer category.
- [x] Add repository CI for the normal `make` target, including proof
  compilation, source-driven assumption auditing, extraction, wrapper tests,
  structural/oracle tests, and optimized-versus-reference differential tests.
- [x] Keep the full benchmark outside the correctness gate; add only a small
  smoke run to CI if its runtime is stable enough for the selected runner.

Exit gate: a fresh checkout automatically checks every claim made for the
current custom API, and the documentation names everything outside that claim.

### N1 — Refine native primitives and representations

Required only for an end-to-end native-refinement claim.

- [x] Specify the 62-bit positive-key domain and logical-to-packed string split
  codec in `NativeRefinement.v`.
- [x] Prove codec validity, injectivity, ordering, valid-token round trips,
  packed `bit_at`, safe bytewise first difference, and the Boolean-XOR
  leading-zeroes source model.
- [x] Prove the bounded source model for native integer shifts, masks,
  prefixes, routing bits, and highest-differing-bit selection.  The
  `native_*_refines` lemmas identify every routing result with the unbounded
  Patricia operation, while the payload/mask lemmas prove the results stay in
  the 62-bit domain.  The link from these mathematical operations to OCaml
  `int` primitives remains a narrowly specified trusted foreign-interface
  obligation, recorded by the mapping audit below.
- [x] Connect OCaml byte length/access and `Char.code` to the source byte model,
  including the guards around `String.unsafe_get`. `NativeRefinement.v` now
  models an OCaml byte string as the `Ascii.N_of_ascii` code array, proves
  length, safe access, guarded unsafe access, and byte bounds, and proves
  `native_packed_bit_at_refines_representation`. The remaining FFI contract is
  narrow and explicit: `String.length` returns the byte-array length,
  `Char.code (String.unsafe_get s i)` returns that array's code whenever
  `i < String.length s`, and short-circuit evaluation preserves the proved
  guards at each access site.
- [x] Prove the native XOR/leading-zeroes first-difference calculation refines
  the source model. `NativeRefinement.v`'s `native_byte_first_diff_correct` and
  `native_string_first_diff_refines` model the realizer's `lxor`/mask-shift
  loop directly (`N.lxor`, `N.land` against `2 ^ (7 - offset)`) and prove it
  finds the same split as the safe `ascii_xor`/`ascii_leading_zeroes` source
  model, hence (via the existing `bytewise_first_diff_correct`) the same split
  as `StringBits.first_diff` itself.
- [x] Audit the remaining standard `positive`, `N`, `nat`, and string extraction
  mappings and record which pieces remain axiomatic or foreign.  The public
  specification now names `ExtrOcamlZInt`, `ExtrOcamlNatInt`,
  `ExtrOcamlNativeString`, and the reference-only `String.length` inline,
  their native representations, and the finite-range or primitive contracts
  still outside the kernel proof.

Exit gate: every low-level native operation used by the optimized map has a
proved refinement theorem or a narrowly specified, explicitly trusted foreign
interface.

### N2 — Refine optimized map algorithms

Required only for an end-to-end native-refinement claim.

- [x] Require cached string branch samples to be resident bindings and prove
  preservation by every smart operation.
- [x] Prove representative independence for consumers of the cached native
  sample, rather than requiring it to equal the pure representative.
  `wf_cached_sample_same_prefix_representative` proves that both selected
  resident keys agree below the branch split;
  `wf_cached_sample_agrees_before_representative` and
  `wf_cached_sample_bit_at_before_representative` carry this to every
  prefix-comparison and strictly-outer routing-bit use in native merge/union.
- [x] Define and prove a source-level one-descent string `set` worker, or verify
  the exception-based native realization in a target-language logic.
  `set_descend`/`set_one_descent` mirror the native exception-based `set`
  realizer's single descend-then-bubble control flow exactly (matched against
  `PatriciaExtract.v`'s `StringPatricia.set` realizer, which caught a real bug:
  the original stub's bubble-caught-here case dropped the sibling subtree and
  the branch's own sample/split, fixed to rebuild the full `Branch`).
  `set_descend_matches_insert_at` proves the descent lands on the same split
  `insert_at` would from a separate top-down `routed_key` pass, using the
  branch-split ordering (`all_splits_after_of_all_keys`) to relate the two
  directions; `set_one_descent_eq_set` concludes `set_one_descent` and `set`
  are the same function, and `set_one_descent_correct_wf` restates wf
  preservation and the `get` law for free by rewriting through it.
- [x] Replace proof-side fuelled `combine` with direct structural recursion
  and prove equivalence to sufficiently fuelled `combine_fuel`.
  `combine_structural` uses nested fixpoints: the outer recursion consumes the
  left tree and the inner recursion consumes the right tree. The compact
  `combine_structural_equation` avoids reducing termination proof terms, and
  `combine_structural_eq_combine_fuel` proves exact agreement with every
  sufficient fuel bound in both backends.
- [ ] Define and prove source-level specialized left- and right-biased unions,
  including their unchanged/disjoint subtree result certificates. The source
  workers, compact proof-facing equation lemmas, and exact
  empty/immediate-join certificates are now defined in the isolated companion
  modules. Both companion closures also prove invariant preservation and the
  left-biased pointwise lookup law for every empty/leaf case. The integer and
  direct-string common-split branch cases are likewise complete; the unequal-
  split routing cases remain open.
- [x] Isolate experimental specialized-union workers in companion Rocq modules
  and give them a targeted extraction/oracle target, so iteration on N2 does
  not invalidate the expensive established `PatriciaProof.v` and
  `StringPatriciaProof.v` proof closures. Integrate a worker into the core
  modules only with its completed refinement theorem. `make union-proof`
  recompiles the companion closure, while `make union-oracle` extracts and
  checks both workers against the established biased unions.
- [ ] Remove the corresponding handwritten `set`, `combine`, and union
  realizers when proved extracted workers meet the performance requirements;
  otherwise prove the realizers against those workers.

Exit gate: optimized public operations are linked by refinement theorems to the
proved finite-map semantics. Physical sharing remains outside the claim unless
N4 is also complete.

### N3 — Optional standard-library map and set APIs

Start only if D3 selects compatibility modules.

- [ ] Prove positive-key `elements` increasing under `Pos.compare`.
- [ ] Prove direct-string `bit_lex_lt` agrees with the selected byte-string
  comparison, including prefix and non-ASCII cases.
- [ ] Prove callback evaluation order for ordered traversals.
- [ ] Add separate `Map.S`-style modules, retaining the current wrappers as the
  proof-oriented API.
- [ ] Cover aliases and basic wrappers first: `add`, `find_opt`, `find`,
  `update`, `equal`, `bindings`, `cardinal`, `iter`, value-only `map`, `mapi`,
  standard-order `fold`, `filter`, and `filter_map`.
- [ ] Add and specify `merge`, conflict-only `union`, `compare`, `partition`,
  extrema/choice, `split`, first/last search, and sequence conversions.
- [ ] Add abstract integer and string set wrappers over unit-valued maps; prove
  membership laws for union/intersection/difference and image laws for
  `map`/`filter_map`.
- [ ] Check the completed modules against the exact `Map.S` and `Set.S`
  signatures of the selected OCaml version.

Exit gate: every exported compatibility operation has its documented
observable semantics, including order and exception behavior. Any physical
identity clause is proved or explicitly excluded from the verified claim.

### N4 — Optional formal cost and sharing model

Start only if D5 selects formal performance claims.

- [ ] Choose a source-level cost model and state what counts as traversal,
  allocation, and subtree reuse.
- [ ] Prove lookup and update bounds in terms of word width or key-bit length.
- [ ] Prove disjoint biased-union and overlapping-merge bounds in terms of
  traversed spines and affected subtrees.
- [ ] Connect source constructor/share certificates to the native heap model
  before claiming physical identity or allocation bounds.

Benchmarks remain useful regression evidence regardless of this track, but do
not close any formal cost theorem.

### N5 — Optional runtime improvements

These are performance features, not verification blockers.

- [ ] Evaluate `set_if_changed` or an equality-aware update that preserves the
  original tree for semantically unchanged values.
- [ ] Add a proved bulk builder such as `of_sorted_list` or `of_sorted_array`.
- [ ] Re-evaluate successful-removal allocation before introducing a native
  physical-child-identity change signal.

### N6 — Optional benchmark hardening

Use this track before making new performance decisions or regression claims.

- [ ] Rerun the bounded-`agrees_before` half-overlap workload at one million
  bindings; only the 10K and 100K post-follow-up results are currently recorded.
- [ ] Calibrate short operations with batched samples and report median and
  dispersion instead of relying on one `Unix.gettimeofday` interval.
- [ ] Add random insertion order, mixed successful/unsuccessful operations,
  subset/no-op/equal/sparse-overlap unions, and adversarial long-prefix strings.
- [ ] Add physical-sharing counters or retained-node checks when a sharing
  decision cannot be supported by allocation totals alone.
- [ ] Time the proof-aligned backend when extraction overhead itself becomes a
  performance question.
- [ ] Pin and report compiler configuration for any comparable benchmark series.

## Completed foundation

- [x] Proved invariant preservation and pointwise laws for every operation in
  the current pure positive-key and direct-string APIs.
- [x] Proved direct-string fresh insertion, separated join, filtering, generic
  combine, both biased unions, and extensional equality.
- [x] Proved lookup/elements correspondence, uniqueness, fold agreement, and
  finite-map extensionality for both variants.
- [x] Proved strong direct-string ordering under the prefix-free bit-stream
  relation.
- [x] Added allocation-free membership, accumulator traversal,
  identity-preserving absent removal, fused combine leaf cases, and bounded
  string prefix scanning.
- [x] Hid raw constructors, fuel/change workers, packed positions, and routing
  helpers behind abstract OCaml wrappers.
- [x] Restricted supported integer keys to positive native integers and made
  the combine absent/absent case unrepresentable.
- [x] Retained a proof-aligned extraction backend and added deterministic
  differential, randomized oracle, invariant, boundary-key, arbitrary-byte,
  and merge-shape tests.
- [x] Added source-driven `Print Assumptions` auditing to the normal build.
- [x] Added checked native benchmarks for operations, allocation, retained
  size, disjoint union, and overlapping union.

## Validation commands

From this directory:

```sh
make
make union-proof
make union-oracle
make benchmark
git diff --check
```

`make` is the functional/proof gate. `make benchmark` is a checked measurement
run, not a deterministic performance threshold.

## Tracking log

| Date | Item | Evidence |
| --- | --- | --- |
| 2026-08-30 | Completed the direct-string specialized-union common-split branch case | `StringPatriciaUnionProof.v`'s `union_left_specialized_same_branch_correct_wf` proves invariant preservation and the full left-biased lookup law from the two recursive contracts, using output-key rebasing to retain the cached-sample invariant. `make union-proof` passed. |
| 2026-08-30 | Proved direct-string common-split output-key invariants | `StringPatriciaUnionProof.v`'s `union_left_specialized_same_split_output_keys` rebases equal-split cached samples and lifts both recursive lookup contracts to the branch-side prefix/bit invariants. `make union-proof` passed. |
| 2026-08-30 | Proved the integer specialized-union common-split composition rule | `PatriciaUnionProof.v`'s `union_left_specialized_same_branch_correct_wf` reconstructs the invariant and pointwise biased-union law from contracts for the two same-split recursive calls. `make union-proof`, `make union-oracle`, and `git diff --check` passed. |
| 2026-08-30 | Proved the specialized-union empty/leaf boundary contracts | `PatriciaUnionProof.v` and `StringPatriciaUnionProof.v` now establish well-formedness and the left-biased pointwise lookup law for every worker case with an empty or leaf operand. `make union-proof`, `make union-oracle`, full `make`, and `git diff --check` passed; the assumption audit reported 311 closed declarations. |
| 2026-08-30 | Isolated specialized biased-union iteration and removed the pathological structural-combine proof reduction | `PatriciaUnion.v`/`StringPatriciaUnion.v` contain nested structural workers; their companion proof files contain the initial exact-result certificates. `combine_structural` was reformulated as nested structural recursion with compact equation lemmas, reducing fresh `PatriciaProof.v` and `StringPatriciaProof.v` compilation from more than 199 seconds at the interrupted unfolding point to under one second each. `make proof`, `make union-oracle`, full `make`, and `git diff --check` passed; the assumption audit reported 307 closed declarations. |
| 2026-08-30 | Replaced the public fuelled combine with a direct structural worker in both backends | `Patricia.v` and `StringPatricia.v` define nested structurally recursive `combine_structural`; their proof files establish exact equality with `combine_fuel` under `combine_fuel_sufficient` and derive the public fuel-bound corollary |
| 2026-08-30 | Completed the N1 byte-string primitive model and guarded-access contract | `NativeRefinement.v` proves `native_bytes_length`, `native_bytes_get`, guarded `unsafe_get` access, `native_code_bit_ascii`, and `native_packed_bit_at_refines_representation`; `make` and `git diff --check` passed |
| 2026-08-30 | Completed the N2 one-descent string `set` worker, fixing a dropped-sibling bug the proof caught in the pre-existing stub | `StringPatriciaProof.v`'s `set_descend_matches_insert_at`/`set_one_descent_eq_set`/`set_one_descent_correct_wf`; full `make`: 281 declarations closed, oracle and differential tests passed; `git diff --check` passed |
| 2026-08-30 | Completed the N1 native XOR/leading-zeroes first-difference refinement | `NativeRefinement.v`'s `native_byte_first_diff_correct`/`native_string_first_diff_refines` connect the realizer's `lxor`/mask-shift loop to the existing safe source model; full `make` and `git diff --check` passed |
| 2026-08-30 | Completed the N1 audit of standard extraction mappings | `SPECIFICATION.md` records the exact imported mapping modules, native representations, and remaining foreign obligations; `git diff --check` passed |
| 2026-08-30 | Completed cached-string-sample representative independence for N2 | `StringPatriciaProof.v` proves prefix, bounded-agreement, and outer-routing-bit equivalence between the cached resident sample and pure representative; full `make` and `git diff --check` passed |
| 2026-08-30 | Completed the bounded integer-routing source refinement for N1 | `NativeRefinement.v` proves prefix, prefix-match, routing-bit, highest-differing-bit, and mask-order correspondence, plus 62-bit payload/mask closure; full `make` and `git diff --check` passed |
| 2026-08-30 | Completed P0: published the current custom-API contract and theorem checklist, enumerated the trusted computing base, added standalone repository CI, and added a bounded checked benchmark smoke target | Clean `make`: 252 declarations closed; randomized oracle and optimized/reference differential tests passed. `make benchmark-smoke`: 100-binding integer and string workloads passed. `git diff --check` passed |
| 2026-08-30 | Resolved D1–D5: pure-model verification claim, unbounded proved domains, frozen proof-oriented API, deferred compatibility with fixed future orders, and empirical performance claims | Decisions checked against the verification boundary and API audit in `patricia.md`; `git diff --no-index --check /dev/null patricia-todo.md` passed |
| 2026-08-30 | Removed the redundant milestone archive; reviewed performance documents and centralized remaining benchmark work under N6 | Documentation reference, status, and whitespace checks passed |
| 2026-08-30 | Created the single active tracker and separated planning from the verification and performance reviews | `make`: 247 declarations closed; randomized oracle and optimized/reference differential tests passed |
| 2026-08-29 | Current custom API proof coverage, abstract wrappers, proof-aligned differential backend, assumption audit, and `NativeRefinement.v` source model completed | Verification summary in `patricia.md`; measurements in `patricia-bench.md` |

## Completion gates

The current pure-model verification claim is complete when:

1. D1–D3 and the public specification are recorded.
2. Every supported pure operation preserves its invariant and has a pointwise
   finite-map law; this is currently satisfied for the custom APIs.
3. Public wrappers enforce all theorem preconditions representable at their
   boundary; this is currently satisfied for map construction, positive keys,
   and combine.
4. Assumption auditing, reproducible extraction, oracle/invariant tests, and
   differential tests pass in repository CI.
5. The native extraction boundary is explicitly excluded from the proof claim
   unless N1 and N2 are complete.

Additional claims use their own gates: `Map.S`/`Set.S` requires N3, physical
sharing or asymptotic complexity requires N4, and an end-to-end optimized
native claim requires N1 and N2.
