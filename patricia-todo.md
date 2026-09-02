# Patricia plan and tracker

Last updated: 2026-09-02

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
- [x] Define and prove source-level specialized left- and right-biased unions,
  including their unchanged/disjoint subtree result certificates. The source
  workers, compact proof-facing equation lemmas, and exact
  empty/immediate-join certificates are now defined in the isolated companion
  modules. Both companion closures also prove invariant preservation and the
  left-biased pointwise lookup law for every empty/leaf case. The integer and
  direct-string common-split branch cases are likewise complete. Both integer
  and direct-string left-outer child-routing reconstruction cases are also
  complete, including the direct-string routing-premise derivation. All
  integer and direct-string branch-shape reconstruction cases are complete.
  Both workers now have their final well-founded structural-recursion
  assemblies and left-/right-biased lookup contracts.
- [x] Isolate experimental specialized-union workers in companion Rocq modules
  and give them a targeted extraction/oracle target, so iteration on N2 does
  not invalidate the expensive established `PatriciaProof.v` and
  `StringPatriciaProof.v` proof closures. Integrate a worker into the core
  modules only with its completed refinement theorem. `make union-proof`
  recompiles the companion closure, while `make union-oracle` extracts and
  checks both workers against the established biased unions.
- [x] Prove source-level models and functional refinements for the remaining
  handwritten `set` and union paths. Both general `combine` realizers have been
  removed: `Patricia.combine` and `StringPatricia.combine` now extract directly
  from the proved structural workers. The companion modules now define and
  extract source-level `union_left_specialized_changed` workers. Both workers
  use `Empty` to mean the original left tree can be reused; every nonempty
  result is rebuilt. The extraction oracle checks both certificate outcomes,
  and both workers have full structural correctness proofs.
  The fuel result wrapper is now proved exactly equal to the established
  changed worker, but the public wrappers deliberately retain the handwritten
  native union realizers. A checked 100K comparison gives the reason: native
  half-overlap allocates 365/81 integer/string words, versus 600,523/600,261
  for the extracted fuel worker; native subset allocates 176/26 and equality
  26/26 integer/string words, while both are linear in the extracted workers.
  Allocation refinement and a formal physical-sharing claim remain open.
  The closure-free experiment now uses one direct worker with a single
  decreasing state: `union_left_specialized_changed_fuel` consumes `fuel` and
  takes both trees as ordinary arguments. Its result wrapper supplies
  `S (size left + size right)` and retains the existing `Empty` reuse
  sentinel. The extracted code has one recursive worker rather than the
  branch-local inner recursion, and the extraction oracle checks its output
  against the established biased union on deterministic and randomized integer
  and string workloads. `make union-profile` now measures both workers without
  changing the supported wrappers. At 100K bindings, the fuel worker retains
  the same constant-size additional result graph and the same left-root reuse
  on subset/equal/no-op inputs, while reducing transient allocation from about
  14 to 12 words per binding on equal, subset, and half-overlap inputs. Its
  preliminary `size` traversal adds only a small fixed allocation in the
  disjoint case, although this is not a time-cost result. Both companion proof
  closures now prove that every fuel strictly above the combined tree size
  agrees exactly with `union_left_specialized_changed`; hence the public
  `S (size left + size right)` wrapper is an exact source-level oracle.
  The next refinement slice is deliberately narrow: model the native worker's
  changed/unchanged outcome by this `Empty` certificate, prove each native
  branch reconstruction has the same pointwise result, and isolate the sole
  heap contract that `child == original_child` permits reusing the enclosing
  original branch. Keep the handwritten realization public until that
  target-language refinement preserves its fixed-allocation behavior. The
  first source fragment is now present: `native_reuse_child` is parameterized
  by a Boolean whose `true` result need only imply lookup equivalence. Both
  companion proofs establish that replacing a recursive child under that
  contract preserves its biased-union result; both equal-header branch
  reconstructions are now closed. The direct-string proof carries the original
  cached sample through left-biased child replacement, so it adds no stronger
  heap assumption. All four integer and all four direct-string containment
  reconstructions now close; the latter preserve cached-sample residency in
  every route. `union_left_native_correct_wf` now assembles the integer
  per-branch certificates into the whole-worker invariant and left-biased
  lookup law; the direct-string theorem of the same name does the same while
  retaining cached-sample residency.
- [ ] Remove the remaining handwritten `set` and union realizers when proved
  extracted workers meet the performance requirements, or link their OCaml
  realizers to those source workers in a target-language refinement. The
  remaining target-level step is to state the OCaml `==` soundness contract
  once for the
  extracted tree type and connect it to the source
  `native_same_sound` assumption. `SPECIFICATION.md` now names the required
  positive-direction contract explicitly. The portable OCaml guarantee for
  non-mutable values is only `compare = 0`, so proving the stronger tree-object
  property requires an OCaml heap/compiler semantics; it remains trusted here.
  A native-shaped Rocq worker now mirrors the handwritten recursion and extracts
  with only `native_same` mapped to `(==)`, but it is not public: at 100K it
  allocates 800,904/800,628 integer/string words for half overlap and
  1,600,788/1,600,948 for equality, despite recovering root reuse. The legacy
  realizer remains at 365/81 and 26/26 words respectively. Its generated
  helper/closure traffic must be eliminated before it can replace the custom
  export.
  The closure-free fuel-shaped native worker was also measured. Passing the
  generic `same` callback through its single recursion made matters worse:
  1,200,993/1,200,634 words on half overlap and 2,400,919/2,400,891 on
  equality. Directly inlining `native_same` and the root/child reconstruction
  checks in that single worker improves the 100K half-overlap allocation to
  1,100,853/1,100,598 words and equality to 2,200,677/2,200,707 words, but is
  still diagnostic-only and remains worse than the nested candidate. The
  remaining routes are (1) retain the fully inlined legacy worker, (2) apply
  an explicit extraction/postprocessing inlining pass, accepting that as a
  small custom build boundary, or (3) keep only the OCaml recursive skeleton
  handwritten and prove/refine its called primitives. None removes the need
  for the target-level `==` contract.
  Mapping `native_same` as an extraction-inline `(==)` primitive and compiling
  with `ocamlopt -inline 1000` did not materially change the profiles. The
  available OCaml 4.14.3 compiler has `flambda: false`; routine compiler
  inlining is therefore not a viable elimination route for this allocation.
  The normally extracted `set_one_descent` worker is also exercised directly
  by the randomized oracle, but a 10K wrapper trial allocated 993,458 versus
  726,896 words for fixed-width-string construction and 1,578,027 versus
  923,171 for updates; the exception realizer remains in the wrapper pending
  a target-language refinement proof or a lower-allocation source worker.

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

- [x] Evaluate `set_if_changed` or an equality-aware update that preserves the
  original tree for semantically unchanged values. `PatriciaBenchmark.ml` now
  measures a benchmark-local lookup-first candidate with an explicit equality
  function. At 10K unchanged updates it preserves the original root and
  allocates 20,030 words for both integer and fixed four-character strings,
  versus 769,162/923,179 for ordinary existing-key updates. It remains local:
  exporting it needs an equality-reflection contract and a proved API addition.
- [x] Add a proved bulk builder. Both abstract wrappers now expose source-level
  `of_list`, whose duplicate policy is explicitly first-binding-wins.
  `of_list_correct_wf` proves invariant preservation and exact pointwise
  agreement with `of_list_get` in both backends. This is a generic batch API,
  not yet a direct sorted builder or a complexity claim.
- [x] Re-evaluate successful-removal allocation before introducing a native
  physical-child-identity change signal. The 10K rerun allocated 452,104
  integer and 588,296 fixed-string Patricia words, versus 433,422 AVL words in
  both cases. The possible saving does not justify widening the extraction
  boundary with a second OCaml physical-identity contract, so removal retains
  the proved `Some changed` signal.

### N6 — Optional benchmark hardening

Use this track before making new performance decisions or regression claims.

- [x] Rerun the bounded-`agrees_before` half-overlap workload at one million
  bindings. The checked four-character run allocated 113 Patricia words versus
  10,193,264 AVL words (7.169 ms versus 23.891 ms); the allocation result
  extends the 10K/100K post-follow-up evidence to one million bindings.
- [x] Calibrate short operations with batched samples and report median and
  dispersion. `PatriciaBenchmark.ml` now measures each union in five samples
  of 32 operations at sizes through 100K (one operation per sample above that
  threshold), reporting the per-union median and min--max range;
  `PATRICIA_BENCH_SHORT_SAMPLES` and `PATRICIA_BENCH_SHORT_BATCH` make both
  parameters explicit and configurable.
- [x] Add random insertion order, mixed successful/unsuccessful operations,
  subset/no-op/equal/sparse-overlap unions, and adversarial long-prefix strings.
  The checked benchmark now uses a deterministic Fisher--Yates insertion
  permutation, a six-way hit/miss/update/remove/add trace, all four additional
  union shapes, and a configurable 192-byte-common-prefix string workload.
- [x] Add physical-sharing counters or retained-node checks when a sharing
  decision cannot be supported by allocation totals alone. `make union-profile`
  now traverses every profiled output, counts its distinct tree nodes, and
  reports how many are physically identical to nodes reachable from each input.
  This distinguishes root reuse from partial subtree reuse without making a
  source-level sharing claim.
- [x] Time the proof-aligned backend when extraction overhead itself becomes a
  performance question. `make reference-profile` natively compiles the ordinary
  extraction in a separate executable, measures build, three lookup passes,
  update, disjoint union, and half-overlap union, and checks each output against
  `Stdlib.Map`. The recorded 1K profile confirms that extraction overhead is
  material, especially for direct strings; the ordinary backend remains a
  differential oracle rather than a runtime candidate.
- [x] Pin and report compiler configuration for any comparable benchmark series.
  CI pins OCaml 4.14.3, while `make compiler-config` emits the version plus
  target-dependent native settings. `patricia-bench.md` records the current
  arm64/Linux, 64-bit, non-Flambda configuration and C compiler flags.

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
make union-profile
make reference-profile
make compiler-config
git diff --check
```

`make` is the functional/proof gate. `make benchmark` is a checked measurement
run, not a deterministic performance threshold.

## Tracking log

| Date | Item | Evidence |
| --- | --- | --- |
| 2026-09-02 | Closed the source-level refinement subtask for handwritten paths | The tracker now separates the completed source models/proofs for native unions and one-descent string `set` from the still-open target-language OCaml realizer link. `union_left_native_correct_wf` closes whole-worker union semantics under `native_same_sound` in both backends; `set_one_descent_eq_set` closes source-level fused-set equivalence. Full `make` passed with 402 closed declarations; the structural differential tests remain in the normal gate. |
| 2026-09-02 | Added structural legacy/native union differential checks | `PatriciaUnionTest.ml` now requires each generated native-shaped worker (nested, fuel, and inline fuel) to be structurally equal to the handwritten legacy union on deterministic and randomized integer/direct-string workloads, in addition to pointwise comparison. This catches a branch-shape or cached-sample difference in the extracted control flow, while remaining finite runtime evidence rather than a target-language refinement proof. `make union-oracle` and `git diff --check` passed. |
| 2026-09-02 | Strengthened exception-based string `set` differential coverage | `PatriciaTest.ml` now requires the handwritten exception realizer and ordinarily extracted `set_one_descent` worker to produce structurally equal trees after every arbitrary-byte randomized update trace, in addition to their existing independent oracle/invariant checks. This makes the runtime differential sensitive to representation differences as well as lookup semantics, but does not prove the OCaml exception/control-flow refinement. `make test`, `make`, and `git diff --check` passed. |
| 2026-09-02 | Added generated-union mutable-payload regressions | `PatriciaUnionTest.ml` now applies every generated native-shaped union worker (nested, fuel, and inline fuel) to overlapping and one-sided `ref` payloads in both backends. It asserts physical identity of selected bindings and observes mutations through the result. This directly guards the workers’ `(==)` sharing paths, but is runtime evidence rather than a proof of `native_same_sound` for OCaml `(==)`. `make union-oracle`, `make`, and `git diff --check` passed. |
| 2026-09-02 | Assembled the direct-string native-shaped union refinement | `StringPatriciaUnionProof.v` now proves `union_left_native_correct_wf`: for any `same` satisfying `native_same_sound`, the full native-shaped worker preserves `wf` (including cached-sample residency) and implements left-biased union pointwise. Together with the positive-key theorem, this completes source-level whole-worker refinement of the handwritten union control flow; the target-level OCaml `(==)` contract remains the sole native-sharing semantic gap. `make StringPatriciaUnionProof.vo` passed. |
| 2026-09-02 | Assembled the integer native-shaped union refinement | `PatriciaUnionProof.v` now proves `union_left_native_correct_wf`: for any `same` satisfying `native_same_sound`, the full native-shaped worker preserves `wf` and implements left-biased union pointwise. Its well-founded combined-size proof applies the existing root/child reuse certificates in every branch relationship. This closes the whole-worker source assembly for positive keys, but does not prove OCaml `(==)` satisfies the premise; direct-string assembly remains open. `make PatriciaUnionProof.vo` passed. |
| 2026-09-02 | Added native-worker unfolding and root-reuse regression coverage | `union_left_native_equation` in each companion source module exposes a complete two-argument recursive step without reducing its nested fixpoint, providing the proof-facing interface for the remaining whole-worker refinement assembly. `PatriciaUnionTest.ml` also verifies physical left-root reuse for empty-right, subset, and equal inputs for every generated native-shaped worker (nested, fuel, and inline fuel) in both backends. These tests are runtime evidence only and do not discharge `native_same_sound`. `make union-proof`, `make union-oracle`, and `git diff --check` passed. |
| 2026-09-02 | Expanded the native-shaped union extraction oracle | `PatriciaUnionTest.ml` now compares the nested native-shaped, generic-fuel native-shaped, and inline-fuel native-shaped workers with the public left-biased union on deterministic and 32 randomized workloads in both integer and direct-string backends. This is runtime evidence for each generated candidate only; it does not establish the `native_same_sound`/OCaml `(==)` contract. `make union-oracle`, `make`, and `git diff --check` passed. |
| 2026-09-02 | Rejected direct source inlining for the generated native union | Both companion modules now expose `union_left_native_fuel_inline_default`, which embeds `native_same` and all root/child reconstruction tests directly in the fuel-decreasing recursion. The extraction oracle checks it on deterministic and randomized integer/string workloads, and `union-profile` measures it beside all other workers. At 100K it reduces generic-fuel half-overlap allocation from 1,200,993/1,200,634 to 1,100,853/1,100,598 words and equality from 2,400,919/2,400,891 to 2,200,677/2,200,707 (integer/string), but remains decisively worse than the nested candidate and legacy 365/81 and 26/26 results. The public wrappers therefore retain the handwritten realizers. `make StringPatriciaUnion.vo`, `make union-oracle`, `PATRICIA_UNION_PROFILE_SIZE=100000 make union-profile`, and `git diff --check` passed. |
| 2026-09-01 | Put native union root reuse in the normal test gate | `PatriciaTest.ml` now asserts that public `union_left` returns the identical first root for empty-right and subset/no-op cases in both integer and string backends. This protects the intended specialized-realizer behavior without making physical sharing part of the formal claim. `make` and `git diff --check` passed. |
| 2026-09-01 | Added mutable-payload biased-union regression checks | `PatriciaTest.ml` now unions maps containing `ref` payloads and asserts physical identity of overlapping preferred bindings and one-sided bindings for both integer and string maps, then observes mutations through the selected result. This guards against accidentally replacing the required payload identity semantics with polymorphic equality in a native union path. It is runtime evidence only and does not establish the OCaml heap/`(==)` refinement contract. `make` and `git diff --check` passed. |
| 2026-09-01 | Completed outer-containment native root-reuse certificates | Both union proof modules now package the two exact root-reuse forms for the right-outer containment routes. Alongside the previously added direct-string root forms and the existing integer equal-/left-outer forms, every physical-root-reuse decision in the native-shaped workers has a kernel-checked invariant and left-biased lookup certificate conditional only on `native_same_sound`. This remains a source-level refinement: it does not prove OCaml `(==)` satisfies that contract. `make PatriciaUnionProof.vo`, `make StringPatriciaUnionProof.vo`, `make union-oracle`, `make assumptions` (398 declarations closed), and `git diff --check` passed. |
| 2026-09-01 | Packaged direct-string native root-reuse refinements | `StringPatriciaUnionProof.v` now proves the exact two-child, left-child, and right-child root-reuse forms used by the native-shaped worker. Each theorem reduces a successful reuse decision to the existing `native_same_sound` positive-direction lookup-equivalence premise; it neither assumes complete equality detection nor establishes OCaml heap behavior, allocation, or physical sharing. `make StringPatriciaUnionProof.vo`, `make union-oracle`, `make assumptions` (394 declarations closed), and `git diff --check` passed. |
| 2026-09-01 | Added proved bulk loading to both supported wrappers | `Patricia.of_list` and `StringPatricia.of_list` recursively use the established `set`, selecting the first duplicate binding. `of_list_correct_wf` proves invariant preservation and pointwise agreement with `of_list_get`; wrapper-oracle checks cover duplicate positive and string keys. This is a generic batch API, not a direct sorted construction or performance claim. `make`, `make benchmark-smoke`, and `git diff --check` passed. |
| 2026-09-01 | Re-evaluated successful-removal allocation | The targeted 10K benchmark measured 452,104 integer and 588,296 fixed-four-character-string Patricia words for removing every binding, versus 433,422 AVL words in each case. The source `Some changed` signal remains selected: a physical-child-identity signal would require the same trusted OCaml heap contract as native union sharing. `PATRICIA_BENCH_SIZE=10000 PATRICIA_BENCH_STRING_LENGTHS=4 PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH=4 make benchmark` and `git diff --check` passed. |
| 2026-09-01 | Evaluated equality-aware unchanged updates | `PatriciaBenchmark.ml` adds a local `get`-then-`set` candidate, validates root identity and map contents, and reports it beside `Stdlib.Map`. At 10K bindings it allocated 20,030 words versus 769,162/923,179 for ordinary integer/fixed-string existing-key updates, so the optimization is useful but remains unexported pending an equality contract and source proof. `make benchmark-smoke`, the targeted 10K benchmark, and `git diff --check` passed. |
| 2026-09-01 | Timed the proof-aligned native extraction | Added `PatriciaReferenceProfile.ml` and `make reference-profile`, a separate native executable because reference and optimized extraction support-module names collide. It checks build, three lookup passes, update, disjoint union, and half-overlap union against `Stdlib.Map`. At 1K bindings, the integer reference build allocated 1,860,582 words versus optimized 33,677; eight-byte string build allocated 19,763,028 versus 56,098. The complete diagnostic table and reproduction commands are in `patricia-bench.md`; `make reference-profile`, matching `make benchmark`, and `git diff --check` passed. |
| 2026-09-01 | Pinned and made native compiler configuration reproducible | CI already pins OCaml 4.14.3; `make compiler-config` now records the version, architecture, model, system, word size, Flambda mode, safe-string mode, and native C compiler flags. The current arm64/Linux configuration is recorded in `patricia-bench.md`; `make compiler-config` and `git diff --check` passed. |
| 2026-09-01 | Added physical subtree-sharing counters to the union profile | `PatriciaUnionProfile.ml` now indexes every nonempty input node by physical identity and reports the output's total nodes plus nodes shared with its left and right input. The diagnostic verifies its output-node traversal against each internal `size` function and remains measurement-only; `make union-profile` and `git diff --check` passed. |
| 2026-08-31 | Completed the source-level native-union sharing cases | `PatriciaUnion.v` and `StringPatriciaUnion.v` contain the source-level child- and one-child-branch reuse model. `native_same_sound` requires only a positive equality test to imply lookup equivalence. Both proof modules close child reuse, equal-header reconstruction, and all four containment routes; direct-string proofs preserve cached-sample residency. Thus every branch shape in the handwritten union has a source refinement conditional on the one `==` soundness contract. `make PatriciaUnionProof.vo`, `make StringPatriciaUnionProof.vo`, and `git diff --check` passed. |
| 2026-08-31 | Extracted the native-shaped union candidate and retained the legacy export | `union_left_native_default` mirrors the full custom branch control flow in both companion modules; only `native_same` is mapped to OCaml `(==)`. The 100K profile recovered subset/equal root reuse but allocated 800,904/800,628 words on half overlap and 1,600,788/1,600,948 on equality (integer/string), versus the legacy 365/81 and 26/26. Both wrappers were restored to the legacy realizers; `union-profile` now displays legacy, generated, proved, and fuel variants and recompiles interfaces safely. `make`, `PATRICIA_UNION_PROFILE_SIZE=100000 make union-profile`, and `git diff --check` passed. |
| 2026-08-31 | Rejected the closure-free native-sharing fuel candidate | `union_left_native_fuel_default` removes the branch-local structural closure but retains a generic `same` callback. At 100K it allocated 1,200,993/1,200,634 words for half overlap and 2,400,919/2,400,891 for equal integer/string inputs—worse than the nested native-shaped candidate. It preserves no-op root sharing but is diagnostic-only; the public wrappers remain legacy. `PATRICIA_UNION_PROFILE_SIZE=100000 make union-profile` passed. |
| 2026-08-31 | Proved the closure-free `union_left` oracle and restored the native realization | `union_left_specialized_changed_fuel_exact` proves that every fuel above the combined source-tree size agrees exactly with the established changed worker; `union_left_specialized_changed_fuel_result_exact` discharges the `S (size left + size right)` bound. The 100K three-way profile showed 600,523/600,261 fuel words for integer/string half-overlap versus 365/81 native words, so both wrappers again select the handwritten native realization. The fuel worker remains the proved source model for the next target-language refinement. `make`, `make union-proof`, `make union-oracle`, `PATRICIA_UNION_PROFILE_SIZE=100000 make union-profile`, and `git diff --check` passed. |
| 2026-08-31 | Profiled the proved and closure-free `union_left` workers | Added `PatriciaUnionProfile.ml` and `make union-profile`, which directly compare the established changed-result worker with the fuel candidate on checked disjoint, half-overlap, subset, equal, no-op, and 192-byte-common-prefix workloads. At 100K inputs the proved/fuel allocations were respectively 700,641/600,523 words for integer half-overlap, 700,524/600,310 for subset, and 1,400,586/1,200,178 for equality; eight-byte strings and long-prefix strings had the same 14-versus-12-word-per-binding pattern. Both retained only roughly 50–90 extra words for changed results and reused the left root for subset, equality, and empty-right. `make union-profile`, `PATRICIA_UNION_PROFILE_SIZE=100000 make union-profile`, and `git diff --check` passed. |
| 2026-08-31 | Added the closure-free changed-worker experiment | `PatriciaUnion.v` and `StringPatriciaUnion.v` now define direct fuel-decreasing changed workers and structural-bound result wrappers. `PatriciaExtract.v` exports them, and `PatriciaUnionTest.ml` checks their deterministic and randomized pointwise outputs. `make union-oracle` and `git diff --check` passed. The workers remain unproved and are not used by public wrappers pending an exact refinement theorem and native allocation profile. |
| 2026-08-31 | Refactored and enabled the direct-string changed-worker sentinel | `StringPatriciaUnion.v` now uses `Empty` rather than `None` as the reusable-left certificate, with `reuse_changed` preserving the original tree only for that sentinel. `StringPatriciaUnionProof.v` proves the interpretation through all equal-header, containment, right-outer, and terminal-join shapes. Both public wrappers now export their proved changed-result workers, and `PatriciaExtract.v` no longer has handwritten biased-union `Extract Constant` overrides. `make`, `make benchmark-smoke`, `PATRICIA_BENCH_STRING_LENGTHS=4 PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH=4 make benchmark`, and `git diff --check` passed. |
| 2026-08-31 | Refactored the integer changed-worker signal to `Empty` | `PatriciaUnion.v` now reuses the nullary tree constructor to represent a match/reusable original tree, eliminating the extracted `option` wrapper. `PatriciaUnionProof.v` proves the sentinel interpretation through equal-header, containment, right-outer rebuild, and terminal-join cases; `PatriciaUnionTest.ml` checks the new signal. `make PatriciaUnionProof.vo`, `make union-oracle`, and `git diff --check` passed. |
| 2026-08-31 | Expanded checked benchmark coverage | Added deterministic random-order builds, a mixed successful/unsuccessful lookup/update/remove/add trace, subset/equal/no-op/sparse-overlap unions, and 192-byte common-prefix strings with `PATRICIA_BENCH_LONG_PREFIX_LENGTH` override. `make benchmark-smoke` and `git diff --check` passed. |
| 2026-08-31 | Calibrated short-union timing | `PatriciaBenchmark.ml` now takes five union samples, batching 32 operations through 100K bindings and one above that size; it reports per-union median and min--max dispersion and accepts explicit sample/batch overrides. `make benchmark-smoke` and `git diff --check` passed. |
| 2026-08-31 | Completed the 1M bounded-string-overlap rerun | `PATRICIA_BENCH_SIZE=1000000 PATRICIA_BENCH_STRING_LENGTHS=4 PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH=4 make benchmark` passed. Four-character half-overlap allocated 113 Patricia words versus 10,193,264 AVL words (7.169 ms versus 23.891 ms); the variable-length checked workload also passed. |
| 2026-08-31 | Measured and retained the native string `set` realizer | Ordinary extraction of `set_one_descent` is now exercised in the randomized structural/oracle test. A checked 10K native trial found its result correct but allocated 993,458 versus 726,896 words for fixed-width-string construction and 1,578,027 versus 923,171 for updates, so the supported wrapper retains the exception realizer. `make`, `make benchmark`, and `git diff --check` passed. |
| 2026-08-30 | Removed handwritten general `combine` realizers | `PatriciaExtract.v` now extracts both proved `combine_structural` workers directly, eliminating the two Patricia-specific merge substitutions. Full `make` passed with 360 closed declarations; `make benchmark` passed, retaining the checked 10K workload's allocation and functional checks. |
| 2026-08-30 | Expanded changed-worker extraction coverage | `PatriciaUnionTest.ml` now runs 32 deterministic mixed-shape workloads per backend, comparing every result against the established left-biased union across 127 keys. `make union-oracle` and `git diff --check` passed. |
| 2026-08-30 | Completed integer changed-worker terminal cases | `PatriciaUnionProof.v` maps all three disjoint branch outcomes to a `Some` separated join: both outer-prefix mismatches and equal masks with distinct prefixes. `make PatriciaUnionProof.vo`, `make union-oracle`, and `git diff --check` passed. |
| 2026-08-30 | Completed integer changed-worker branch reconstruction | `PatriciaUnionProof.v` now has changed-result certificates for equal headers and all four unequal-mask routing sides. The right-outer rules account for the mandatory enclosing-branch rebuild. `make PatriciaUnionProof.vo` and `make union-oracle` passed. |
| 2026-08-30 | Proved integer changed-worker equal-header reconstruction | `PatriciaUnionProof.v`'s `union_left_specialized_changed_same_branch_correct_wf` handles all four optional child-result shapes, using `branch_unchanged` for the all-unchanged certificate. `make PatriciaUnionProof.vo` passed. |
| 2026-08-30 | Completed direct-string changed-worker refinement | `StringPatriciaUnionProof.v` now proves `union_left_specialized_changed_correct_wf` and its right-biased dual by the same combined-size induction as the specialized worker, reusing the changed-result branch certificates. Full `make` passed with 352 closed declarations. |
| 2026-08-30 | Fixed changed-worker right-outer rebuilding | Both source-level changed workers now rebuild an enclosing right branch even when the recursively routed child is unchanged; otherwise the outer sibling was lost. `PatriciaUnionTest.ml` includes integer and string regressions for that shape. `make union-oracle` passed. |
| 2026-08-30 | Proved direct-string changed-worker left-outer reconstruction | `StringPatriciaUnionProof.v` now covers both left- and right-child containment routes. In an unchanged-child path it preserves the raw cached branch while using representative-independent lookup equivalence. `make StringPatriciaUnionProof.vo` and `make union-oracle` passed. |
| 2026-08-30 | Proved direct-string changed-worker equal-split reconstruction | `StringPatriciaUnionProof.v`'s `union_left_specialized_changed_same_branch_correct_wf` normalizes all four optional child-result shapes through the established branch reconstruction theorem. Its `None`/`None` path proves lookup preservation despite cached-sample reuse. `make union-oracle` passed. |
| 2026-08-30 | Added compact changed-worker equations | `PatriciaUnion.v` and `StringPatriciaUnion.v` now provide `union_left_specialized_changed_equation`, exposing one recursive step without expanding the nested local fixpoint. This unblocks induction-hypothesis rewriting in the remaining branch/branch proof. `make union-oracle` passed. |
| 2026-08-30 | Proved changed-worker boundary equivalence | `PatriciaUnionProof.v` and `StringPatriciaUnionProof.v` now show the changed-result worker agrees definitionally with the established specialized worker for empty and leaf operands. The outstanding changed-worker refinement proof is isolated to branch/branch cases. `make union-oracle` passed. |
| 2026-08-30 | Implemented source-level changed-result union workers | `PatriciaUnion.v` and `StringPatriciaUnion.v` now define `union_left_specialized_changed`, its result wrapper, and right-biased duals; `PatriciaUnionTest.ml` checks both unchanged and changed certificates after extraction. A temporary 10K wrapper benchmark measured 70,305 integer and about 70,240 fixed-length-string overlap words, versus 81,324 for AVL. Correctness proofs for the new workers remain the next N2 task, so the experiment did not replace the supported handwritten union. |
| 2026-08-30 | Evaluated extracted specialized unions for the supported wrappers | The fully proved `PatriciaUnion` and `StringPatriciaUnion` workers pass `make union-oracle`, but a 10K native benchmark trial allocated roughly 100K/110K words for integer/string overlap, losing the handwritten unions' physical-identity reuse. The public wrappers therefore continue to use the tested handwritten optimization; the final N2 realizer-refinement obligation remains open. |
| 2026-08-30 | Completed the integer specialized-union correctness assembly | `PatriciaUnionProof.v` now proves `union_left_specialized_correct_wf` and its right-biased dual by combined-size induction. Its three terminal-join certificates cover equal masks with distinct prefixes and each unequal-root mismatch. `make union-proof` passed. |
| 2026-08-30 | Completed the direct-string specialized-union correctness assembly | `StringPatriciaUnionProof.v` now proves `union_left_specialized_correct_wf` and its right-biased dual by well-founded induction on combined tree size, consuming the existing equal-split, containment, and separated-join certificates. `make union-proof` passed. |
| 2026-08-30 | Proved the direct-string specialized-union disjoint terminal case | `StringPatriciaUnionProof.v`'s `union_left_specialized_disjoint_branches_correct_wf` converts the worker’s failed bounded-prefix comparison into the existing separated-join invariant and left-biased lookup contract. `make union-proof` passed. |
| 2026-08-30 | Established the specialized-union assembly measure | Both companion proof files now prove that each of the six branch/branch recursive pair shapes strictly decreases combined tree size, providing the well-founded measure for the remaining global worker theorem. `make union-proof` passed. |
| 2026-08-30 | Completed the integer right-outer unequal-split reconstruction | `PatriciaUnionProof.v` adds left- and right-child reconstruction rules for the inner structural recursion, completing the four integer unequal-split branch shapes. `make union-proof` passed. |
| 2026-08-30 | Proved direct-string right-outer unequal-split reconstruction | `StringPatriciaUnionProof.v` adds left- and right-child reconstruction rules for the branch held by the worker’s inner structural recursion. `make union-proof` passed. |
| 2026-08-30 | Derived direct-string left-outer routing from the worker test | `StringPatriciaUnionProof.v`'s `union_left_specialized_left_outer_routing` turns the successful `agrees_before_bounded` check and split ordering into the exact all-keys side invariant consumed by the unequal-split reconstruction rules. `make union-proof` passed. |
| 2026-08-30 | Proved direct-string left-outer unequal-split reconstruction | `StringPatriciaUnionProof.v` adds the left- and right-child reconstruction rules, each proving well-formedness and the biased lookup law once the branch-side routing invariant is supplied. `make union-proof` passed. |
| 2026-08-30 | Completed both integer left-outer unequal-split child routes | `PatriciaUnionProof.v` adds `union_left_specialized_left_outer_right_branch_correct_wf`, complementing the left-child reconstruction rule. `make union-proof` passed. |
| 2026-08-30 | Proved the first integer unequal-split routing reconstruction | `PatriciaUnionProof.v`'s `union_left_specialized_left_outer_branch_correct_wf` proves the invariant and pointwise left-biased law when the complete right operand lies in the left child of an outer left branch. `make union-proof` passed. |
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
