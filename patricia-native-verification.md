# Patricia native verification gaps and tracker

Last updated: 2026-09-09

This document owns the detailed inventory and forward tracker for reducing
unverified native code without sacrificing performance. The project-wide
decisions and N1/N2 history remain in [patricia-todo.md](patricia-todo.md).
[SPECIFICATION.md](SPECIFICATION.md) remains authoritative for public claims;
this plan does not expand them. The verification review is in
[patricia.md](patricia.md), and measurements belong in
[patricia-bench.md](patricia-bench.md).

## Objective and boundaries

The current claim is kernel-checked functional correctness of the pure Rocq
maps. The supported OCaml implementations are tested refinements, with explicit
trust in extraction, native mappings, handwritten realizers and the runtime.
There is no proved native cost or sharing guarantee.

The immediate objective is to remove handwritten algorithm substitutions, or
prove the executing algorithms against a target-language semantics, while
preserving native representations, traversal behavior and allocation. Removing
lines of OCaml is not itself a proof improvement: moving them into an unchecked
postprocessor or adding an axiom transfers trust rather than discharging it.

Keep the unbounded positive-key and logical-string public models (D2). A
separate executable implementation model with representation relations is
compatible with this decision. A change to the public domains or verification
claim is a separate project decision.

Distinguish three milestones:

1. Proved executable algorithms, extracted with a small, enumerated primitive
   interface. Ordinary extraction and those primitive contracts remain trusted.
2. Target-level algorithm refinement, including representations and physical
   equality. The selected translator/compiler/runtime can still remain trusted.
3. Verified compilation and runtime connections sufficient for the precise
   end-to-end claim being proposed. Neither milestone 1 nor an abstract heap
   lemma alone establishes this milestone.

## Inventory of unverified code

The 2026-09-09 post-union audit now finds 14 explicit replacement directives in
[PatriciaExtract.v](PatriciaExtract.v). This is a source inventory, not a count
of distinct algorithms or a measurement of reachable machine code. Two
directives supply physical equality only to the source-defined direct union
workers; the public wrappers select those extracted workers.

| ID | Component and amount | Function and performance purpose | Existing proof support | Remaining obligation |
| --- | --- | --- | --- | --- |
| I1 | Nine integer directives: `Pos.eqb`, `N.eqb`, `N.ltb`, `word`, `prefix`, `matches_prefix`, `zero_bit`, `highest_differing_bit`, `mask_above` | Native comparisons, shifts, masks and XOR implement routing and split selection without recursive arithmetic on inductive numbers. | `NativeRefinement.v` proves bounded mathematical routing correspondence and 62-bit key/mask closure; `native_routing_shift_count_fits` covers routing and prefix shift counts; `native_log2_loop_correct` proves the fuelled source model of the right-shifting accumulator loop, while `native_highest_differing_bit_loop_correct` applies its 62-step instance to bounded XOR operands. | Relate actual native operators and the right-shifting `log2` loop to that model and target operators. |
| I2 | `StringBits.bit_at` | Decode packed byte/tag positions and inspect a byte directly. | Codec validity, ordering, round trips, byte-array access laws and `native_packed_bit_at_refines_representation`. | Prove or retain explicit contracts for native strings, integer token decoding and guarded byte access. |
| I3 | `StringBits.first_diff` | Scan bytes by index, use XOR and a mask loop for the first differing bit; identical string objects return immediately. | Safe structural bytewise scanner and `native_string_first_diff_refines`; per-byte XOR/leading-zeroes laws; `native_string_first_diff_with_identity_refines` proves the identity shortcut under `native_string_same_sound`. | Prove the indexed loop, counter progression and mask progression implement the model; establish the OCaml-string physical-equality contract and primitive execution correspondence. |
| I4 | `StringBits.agrees_before_bounded` | Scan only the bytes/high bits before the split; return a Boolean without allocating a first-difference option. | `native_bounded_prefix_scan_correct` (2026-09-10) refines the indexed source byte scan to `agrees_before_bounded`; its proof covers complete bytes, continuation markers, terminal partial tags, the shorter-length sentinel, short-circuiting and byte-count termination. `native_terminal_mask_equal_correct` proves the emitted terminal `lxor`/left-shift/`land` expression equal to the high-bit iterator for every valid tag 1–8. | Connect the extracted OCaml loop's integer/string primitives and execution—including guarded unsafe access—to these source models. |
| I5 | Resolved 2026-09-09: former `StringPatricia.representative` directive | Read a cached sample in constant time instead of descending to a leaf. | Cached-sample residency/independence lemmas; proved cached filtering, deletion, generic combine, and selected `Acc` union refinements. | The override is removed. `cached-representative-audit` forbids its reintroduction; the total structural source definition remains for raw-tree proofs. |
| I6 | Resolved 2026-09-09: former four handwritten union directives | Public wrappers call extracted `union_*_native_acc_default` workers; direct `Acc` recursion replaces fuel and nested closures while retaining reuse decisions. | `union_left_native_acc_exact` and left/right well-formedness/lookup theorems in both companion proof files. | No handwritten high-level union body remains. I7's `(==)` adequacy, primitive contracts, extraction/compiler/runtime and allocation semantics remain separate obligations. |
| I7 | Two selected `native_same => (==)` directives | Connect source-defined native-shaped workers to physical equality. | `NativeHeapRefinement.v` derives source soundness from a per-call object/heap adequacy contract. | Establish that target execution supplies this contract. These directives are separate from the native string identity shortcut in I3. |
| I8 | Standard `ExtrOcamlZInt`, `ExtrOcamlNatInt`, `ExtrOcamlNativeString`/`ExtrOcamlChar` mappings | Represent numbers and byte strings natively. | Source domain/codec models and the mapping audit in `SPECIFICATION.md`; integer routing has 62-bit closure, while packed string tokens require `16 * length + 8 < 2^62`. | Establish that the runtime supplies the packed-length and primitive contracts for all reachable strings/counters. The reference backend shares these mappings. |
| I9 | `PatriciaMap.ml` and `StringPatriciaMap.ml`: 95 lines in total at the 2026-09-10 audit | Abstract map/key interfaces, positive-key validation, aliases, and the restricted combine adapter. | The `.mli` files abstract map/key types; `check_abstract_interfaces` exercises invalid/maximum integer keys, aliases, all three combine cases, and binary string keys. | Prove/extract the adapter and relate key validation to the native key domain, or verify the small wrappers directly. Abstract signatures and build visibility still need a semantic—not merely compilation—argument. |
| I10 | Extraction, module renaming/packing/linking, OCaml compiler/runtime and host platform | Produce and execute the library, including GC and native primitive operations. | Build checks, generated-body audits and a pinned compiler-source equality audit. | Explicitly retain these assumptions, or connect the appropriate verified extraction/compiler/runtime results. A syntactic audit is not a simulation proof. |

Ordinary extraction already handles general `combine`, public string `set`,
lookup, membership, removal, mapping/filtering, bulk `of_list`, fold and
elements. There is no remaining handwritten general-merge or exception-based
string-insertion realizer. These operations still depend on I1–I5/I8/I10 as
applicable. Experimental workers, test oracles and benchmark code are useful
evidence; they are not additional public map algorithms whose functional
correctness must be proved to establish the current API laws.

## What the existing proofs do not establish

### Representations must be related, not identified

Logical string position `9*b+t` is represented by packed token `16*b+t`.
For example, logical position 9 is token 16. Comparing the two `bit_at`
implementations at the same integer argument is therefore the wrong theorem.
The implementation relation must also preserve split order and valid tags.

Similarly, a cached resident sample may differ from the leaf chosen by the
pure representative. Use resident-key and prefix/routing independence laws;
do not demand representative equality or replace callers without proving the
needed consumer relation.

The source first-difference model traverses logical string tails; the native
code indexes byte arrays and shifts a mask. Their common result specification
does not by itself prove equivalence of those control flows. The bounded prefix
loop I4 needs its own proof, not just a reference to the logical scanner law.

### A physical-equality premise is not an OCaml execution proof

`native_same_sound` needs only the positive direction: a successful test
permits substituting a tree with the same lookups. Failure may cause rebuilding.
`NativeHeapRefinement.v` proves that adequate current runtime objects and a
same-root test suffice. It does not simulate recursive union execution,
allocation or moving GC, nor prove that the handwritten bodies call primitives
with the required representations.

Payloads are unrestricted, including mutable objects and functions. Do not
replace pointer tests by polymorphic structural equality or assume that
`compare = 0` proves payload identity. Physical-equality subtleties are treated
explicitly by Allain and Scherer [R2](#r2-zoo). For this project, proving a
stronger pinned-runtime contract is distinct from specifying portable OCaml.

### Current performance evidence is about allocation

The rebuilt 10K profile on 2026-09-09 used Rocq 9.2 and OCaml 4.14.3,
arm64/Linux, 64-bit, `flambda: false`. Integer half-overlap allocated 243 words
in the public union versus 80,287 in the generated native-shaped worker;
strings used 86 versus 80,126. Equal inputs used 26 versus 160,016 words for
both backends. The measured workers retained the same input-node sharing in
these cases. See the [dated measurement record](patricia-bench.md#native-verification-investigation-2026-09-09).

Generated nested recursion returns capturing functions. Generated fuel workers
pass capturing callbacks to the native-`nat` eliminator, even after helper and
equality inlining. These are concrete allocation candidates visible in the
generated code, not a complete compiler-level allocation attribution.
The fuel wrapper also traverses both inputs to compute their sizes. A small
allocation count would not make that prepass acceptable for disjoint union.

The earlier failure of `ocamlopt -inline 1000` on a non-Flambda compiler does
not rule out a Flambda build or recursion whose proof argument erases entirely.
None of these measurements establishes elapsed-time equivalence for a proposed
replacement, nor constant allocation for every possible overlap shape.

## Strategies and order of investigation

| Strategy | Gaps addressed | Expected performance effect | Trust remaining / decision |
| --- | --- | --- | --- |
| S1: Explicit recursion on an accessibility proof in `Prop` | I6, then possibly I3/I4 loop control | Aim for one saturated recursive function, no runtime fuel/size prepass, and no branch-local recursive closure. | Keep primitive and `==` contracts initially. First experiment; success must be measured. [R1](#r1-erased-termination-proofs) |
| S2: Proved native implementation layer over small primitive interfaces | I1–I5, I8 | Preserve packed positions, indexed byte scans, cached reads and native word operations. | Primitive implementations and ordinary extraction remain explicit assumptions. Develop alongside S1. |
| S3: Deductive verification of the existing OCaml bodies | I6/I7, potentially I1–I5/I9 | Preserve executing algorithm/code shape where the verifier accepts it; proof work need not add runtime work. | Account for frontend translation, language semantics, primitives and compiler/runtime trust. Main alternative if S1 fails. [R2](#r2-zoo), [R3](#r3-characteristic-formulae) |
| S4: Flambda specialization or controlled extraction optimization | Closure traffic in I6 | May remove known callbacks and intermediate closures. | Flambda stays in the compiler TCB. An unchecked custom postprocessor adds trust; a proved transformation or checked certificate can avoid that addition. Diagnostic alternative, not proof by benchmarking. |
| S5: Verified extraction to Malfunction | Part of I10 | Potentially preserves OCaml interoperability; performance for these maps is unmeasured. | Does not validate arbitrary `Extract Constant` strings or remove Malfunction/OCaml compiler and FFI assumptions. Longer-term integration. [R4](#r4-verified-extraction) |
| S6: Extract or verify the small wrappers | I9 | Aim to retain the same aliases and adapter without new allocations. | Abstract interface/build enforcement and primitive validation contracts remain. Small follow-up, lower priority than the recursive algorithms. |

### S1: Erase termination, rather than represent it as runtime fuel

Use explicit structural recursion on `Acc` in `Prop`, with the combined tree
size used only in the termination relation/proofs. Reuse the six branch-pair
decrease lemmas already available in each companion proof file. Keep the two
trees as ordinary parameters: introducing an executable pair solely for the
termination argument can itself create allocation.

First extract a small candidate and inspect its OCaml shape. Then establish
its compact equation and functional equivalence/refinement against the existing
native-shaped worker under `native_same_sound`. Both argument orderings must
meet the biased-union laws. Use standard extraction inlining where needed;
prove algorithm changes in Rocq rather than silently rewriting generated code.
Leroy's example explains why the accessibility proof can disappear while
ordinary direct recursion remains [R1](#r1-erased-termination-proofs).

A second candidate can use the existing `Empty` unchanged-result certificate
to avoid tree `==`. Its immediate sentinel need not allocate, but the current
certificate promises reuse of the left operand only. It does not automatically
recover all containing-right-tree reuse cases. Require those cases and changed
result allocation in the comparison before claiming to eliminate I7 without
sacrificing performance.

### S2: Extract executable control flow, keep primitive assumptions small

Begin with I5's cached reader and I4's bounded byte scanner. For I4, specify the
relation between the scan index, split byte/tag, matched prefix and current
byte bounds; prove termination and each partial-byte/end-marker case. Use
length/index operations rather than extracting recursive native-string tails
that may copy substrings. For I3, add an indexed-scan invariant and prove the
shifting-mask loop and identity shortcut against the existing first-difference
specification. Preserve tail calls and allocation-free Boolean prefix checks.

For I1/I8, enumerate the actual primitive calls and prove range closure at
each use, including packed-token construction, logical positions and traversal
counters where reachable. A primitive interface can be parameterized in Rocq;
the theorem should expose its assumptions clearly. Importing `Uint63` alone
does not discharge foreign implementation obligations; the
[Rocq primitive-object manual](https://rocq-prover.org/doc/v9.2/refman/language/core/primitive.html)
documents primitive assumptions and the supplied OCaml mapping boundary.

### S3–S5: Check integration before committing to a new toolchain

CFML verifies ML programs through characteristic formulae; the foundational
approach is described in [R3](#r3-characteristic-formulae). The
[current CFML README](https://github.com/charguer/cfml) documents OCaml below 5
and testing with Coq 8.20, so compatibility with this Rocq 9.2 checkout remains
to be established. Zoo's OCaml 5 fragment and physical-equality semantics are
particularly relevant [R2](#r2-zoo). Neither option should be assumed to supply
the exact bounded integer, native string, arbitrary-payload or compiler/GC
contracts needed here. Start by verifying one actual containment/reuse branch
with its called primitive specifications, then extend to the whole worker.

A real Flambda build is a separate experiment from the existing compiler flag
trial. Its [documented recursive specialization](https://ocaml.org/manual/5.2/flambda.html)
is relevant to the invariant `same` argument. Compare both public and candidate
workers on each compiler; do not attribute an across-compiler speedup solely
to the candidate.

Verified extraction [R4](#r4-verified-extraction) reduces the erasure/extraction
boundary, not every downstream assumption. The
[project documentation](https://github.com/MetaRocq/rocq-verified-extraction)
also marks optional inlining and several other optimizations as unverified.
Check the selected version's exact theorem, options, interoperability domain
and compatibility with our callbacks/polymorphic payloads before relying on it.

## Separate tracker

This section owns new detailed native-verification tasks. Do not duplicate its
checkboxes in the main tracker. `[x]` means completed with recorded evidence;
`[ ]` means open; `[-]` means deferred. Alternatives need not all be completed.
No implementation strategy below has yet passed its replacement gate.

### V0 — Establish the baseline

- [x] V0.1 Inventory explicit substitutions, shared standard mappings, wrappers
  and compilation/runtime trust; distinguish public and experimental workers.
- [x] V0.2 Inspect generated nested/fuel recursion and reproduce the checked
  10K allocation/sharing comparison on the pinned compiler.
- [x] V0.3 Record publication references and separate source-model proofs from
  actual OCaml loop/worker refinement obligations.

### V1 — Union replacement experiment (S1; parent N2)

- [x] V1.1 Extract an integer `Acc`-recursive candidate; verify no operational
  size prepass, fuel eliminator, termination tuple or per-node recursive closure.
  `union_left_native_acc` extracts to one direct recursive OCaml function; the
  2026-09-09 10K profile exactly matched the legacy worker's allocation and
  root-reuse figures on the integer workloads.
- [x] V1.2 Prove its equation and left/right lookup and well-formedness laws
  under the explicit primitive/equality premises; audit assumptions. The exact
  refinement and both biased laws are in `PatriciaUnionProof.v`; the only
  non-source premise remains `native_same_sound` for target `(==)`.
- [x] V1.3 Repeat for strings, carrying packed positions and cached residency.
  `StringPatriciaUnion.union_left_native_acc` has the same direct extracted
  shape and matched legacy allocation/root reuse on both ordinary and
  192-byte-common-prefix 10K workloads. Its refinement reuses the established
  packed-position and cached-sample source contracts; it does not claim to
  discharge their native OCaml primitive obligations.
- [x] V1.4 Evaluate the changed-result alternative, including right-operand
  containment/reuse; document whether eliminating `==` is actually competitive.
  The proved changed-result worker is not competitive: at 10K, its
  integer/string half-overlap allocations were 70,283/70,146 words versus
  243/86 for `Acc`; equal trees were 140,017/140,017 versus 26/26. It cannot
  retain enclosing roots when its data sentinel distinguishes no-change from a
  real branch result, so it does not replace I7.
- [x] V1.5 Select the proved public worker and remove both backends' two union
  directives. `PatriciaMap.ml` and `StringPatriciaMap.ml` select the `Acc`
  defaults; the extraction-boundary audit requires zero high-level union
  overrides, and the native-worker audit verifies direct recursion with no
  runtime size/fuel argument or nested recursive closure. Correctness,
  native-oracle, differential, public-wrapper, and 10K/100K allocation/share
  checks are recorded below. Timing/GC cost theorems remain N4, not evidence
  silently claimed by this selection.

### V2 — Native primitives and cached representatives (S2; parent N1/N2)

- [x] V2.1 Integrate a source-defined cached representative with proved
  consumer refinement, then remove I5's override after performance validation.
  Groundwork completed in `8fc60a6`: `representative_cached` and its
  `wf`-resident/nonempty refinement theorems are source-defined. The override
  intentionally remains because migrating all consumers (notably `join` and
  public update paths) is required before comparing performance safely. The
  migration sequence is: retain total `representative` for raw-tree lemmas;
  add cached `branch`/`join` counterparts; prove their `wf` lookup and
  well-formedness refinements; migrate each public operation and benchmark it;
  only then remove I5's override. `branch_cached` is complete with
  `branch_cached_nonempty_wf`, `branch_cached_wf_general`, and
  `get_branch_cached`; `join_cached` is complete for separated inputs with
  `join_cached_separated_correct_wf`. The first public migration is now
  complete: `map_filter_cached_wf` and `get_map_filter_cached_wf` prove the
  cache-aware traversal, extraction shows direct recursion through
  `branch_cached`, and `StringPatriciaMap.map_filter` selects it. The
  `map_left`/`map_right` helpers and both fused leaf-combine workers now
  delegate to that traversal as well, so their existing contracts cover the
  cache-aware one-sided combine cases. `remove_cached_wf` and
  `get_remove_cached` establish the same deletion contract, and the public
  wrapper plus `replace_binding` select its direct extracted changed-result
  worker; the public test checks absent-key root reuse. `make map-filter-profile` and
  `make remove-profile` validate the legacy override, extracted cached worker,
  and public wrapper against their bindings: on the pinned compiler, all three
  allocations match at 10K and 100K for the filter's keep-all, keep-even, and
  drop-all workloads and removal's absent/present workloads. Generic
  `combine_fuel` and `combine_structural` now use `branch_cached` for every
  recursive branch construction and `join_cached` for every separated fallback;
  their original pointwise and `wf` contracts are re-proved through
  `combine_join_cached_separated_correct_wf`. Selected `Acc` union now uses
  `join_cached` in all three separated fallbacks; its exact source-worker
  theorem and cached disjoint-branch refinement preserve the biased contract.
  The extraction gate
  `make cached-representative-audit` verifies generated direct cached calls in
  removal, filtering, both generic combine workers, and selected `Acc` union.
  The manifest audit forbids reintroducing the former representative directive. Raw-tree
  proof references deliberately retain the total source reader.
- [-] V2.2 Model the executable indexed bounded-prefix scan for I4. The
  2026-09-10 source model now follows its complete-byte, shorter-length
  sentinel, terminal-tag and partial-code control flow;
  `native_complete_byte_equal_guarded` and
  `native_prefix_tag_equal_guarded` make every modelled unsafe read depend on
  both length guards, while `native_prefix_code_equal_spec` and
  `native_prefix_tag_equal_terminal_spec` specify the terminal high-bit and
  continuation-marker comparison; `native_complete_byte_equal_complete_spec`
  gives the same logical-position account for its recursive byte branch.
  `native_common_sentinel_spec` establishes the minimum-length sentinel
  invariant, and `native_bounded_prefix_scan_correct` composes all branches
  into the `agrees_before_bounded` refinement.
  `native_terminal_mask_equal_correct` proves the mathematical terminal
  `xor`/mask expression equal to the high-bit iterator for every valid tag;
  it factors the finite one-difference-byte mask theorem from the XOR-code
  bridge rather than enumerating tag/byte-pair combinations. Remaining:
  connect OCaml primitives, guarded unsafe access and execution to these
  models.
- [-] V2.3 Prove indexed first difference and its shifting-mask/identity paths
  for I3; compose with the existing logical first-difference theorem.
  The source-model portion is already closed by
  `native_byte_first_diff_correct`, `native_string_first_diff_correct`, and
  `native_string_first_diff_refines` in `NativeRefinement.v`: byte XOR,
  leading-zero mask shifts, and packed-position composition are proved.
  `native_string_first_diff_with_identity_refines` now verifies the
  source-level early-return path under the explicit positive-direction
  `native_string_same_sound` contract. Still open is a target-execution
  refinement of the indexed OCaml scan and the physical-equality/native
  string/int contracts.
- [-] V2.4 Audit reachable integer/string intermediates and prove range closure;
  give each retained native operator/byte access an explicit foreign contract.
  Integer routing closure is already proved at 62 bits, and
  `native_log2_loop_correct` establishes the source loop invariant: whenever
  `log2 value < fuel`, the fuelled right-shift accumulator returns
  `accumulator + log2 value`; `native_log2_loop_native_word_correct` instantiates
  it with the realizer's fixed 62-step fuel for every native-word value. The
  `native_lxor_log2_fits_native_word` and
  `native_highest_differing_bit_loop_correct` close that source-fuel argument
  for the realizer's bounded XOR input. `native_routing_shift_count_fits`
  similarly closes the source count bound for the `mask` and `mask + 1`
  shifts. The 2026-09-10 audit
  identifies the remaining string precondition precisely: a packed token at
  byte index `length` and tag 8 fits only if `16 * length + 8 < 2^62`.
  `native_packed_position_fits_string_capacity` now proves every end-inclusive
  valid token fits once `native_string_packed_capacity` holds;
  `native_byte_index_fits_string_capacity` and
  `native_scan_successor_fits_string_capacity` cover guarded byte indices and
  the scan increment. OCaml's `String.length`, allocation limits and native
  `nat` arithmetic have not yet been connected to that contract.
- [-] V2.5 Extract the proved control flow and remove corresponding overrides
  only after checking native code shape and the full performance gate. A
  2026-09-10 candidate extraction of `native_string_first_diff` was rejected:
  generated native-string elimination recursively called
  `String.sub s 1 (l - 1)`, copying a suffix per byte, and emitted an empty
  `String` unit that shadowed `Stdlib.String`. It was not selected or retained;
  a viable candidate must preserve indexed constant-time byte access.

### V3 — Target-language refinement (S3; parent N2)

- [ ] V3.1 Compare CFML/Zoo or a small target semantics using one actual union
  containment/reuse case; record supported syntax and exact remaining TCB.
  Environment audit on 2026-09-09 found no installed CFML, Zoo, Malfunction,
  or verified-extraction package; CFML's documented Coq 8.20 compatibility
  also remains distinct from this Rocq 9.2 checkout. No unavailable tool is
  represented as target-level evidence.
- [ ] V3.2 Define the target-tree/payload representation relation and prove
  the physical-equality adequacy used by each recursive reuse decision.
- [-] V3.3 Prove the complete selected OCaml worker, its dependencies and
  swapped right bias against the source laws. This became inapplicable to I6
  when V1.5 removed the handwritten worker bodies. A target-level proof is
  still relevant only for I7's physical-equality adequacy and the remaining
  primitive/compiler boundary, covered by V3.2/V3.4.
- [ ] V3.4 Compose operation-level target refinements and record remaining
  compiler/runtime assumptions before revising any public verification claim.

### V4 — Alternative extraction and small boundaries

- [ ] V4.1 Benchmark a genuine Flambda build with the same source/workloads;
  record allocation, timings and specialization reports (S4).
  The pinned OCaml 4.14.3 toolchain reports `flambda: false` on arm64 Linux;
  no non-Flambda run is labelled as satisfying this item.
- [ ] V4.2 Assess verified extraction with a small integer-map entry point and
  explicit primitives; audit options and interoperability before expansion (S5).
  No verified-extraction toolchain is installed in the pinned environment;
  this remains a separately provisioned experiment, not an alternative label
  for ordinary Rocq extraction.
- [ ] V4.3 Extract/prove the combine adapter and key-validation relation, or
  verify the wrappers directly; preserve abstract interfaces (S6). The
  2026-09-10 audit confirms 95 implementation lines and opaque `.mli`
  boundaries, while `check_abstract_interfaces` covers the public cases;
  neither is a proof of wrapper semantics.
- [-] V4.4 Develop a custom extraction postprocessor only if simpler routes
  fail; require a proved transformation or certificate checker to claim a TCB
  reduction, otherwise label it an additional trusted build step.
- [-] V4.5 Formal cost, allocation and GC/sharing semantics remain the separate
  N4 expansion. Time credits [R5](#r5-cost-reasoning) are relevant methodology,
  not a theorem about this program's native allocation or collector.

## Replacement and closure gates

1. Correctness: prove the candidate's law and invariants, then run `make`,
   `make union-oracle` and `make union-oracle-native` as applicable. Retain
   differential and structural tests and native key/byte boundary cases.
   Exercise conflicting values, distinct mutable payloads and function payloads
   without structural payload comparison, plus GC-sensitive reuse cases.
2. Execution shape: inspect generated OCaml and, where necessary, compiler
   output for recursive arity, closures, eliminator callbacks, tuple/result
   wrappers, substring copying and unconditional input traversals.
3. Performance: compare the public implementation and candidate on the same
   compiler/machine at 10K and 100K, then larger runs as resources permit.
   Include disjoint, half/sparse overlap, subset, equal, independently built
   equal-key trees, empty operands, both biases, all containment directions,
   random insertion, and long-prefix/binary strings. Check elapsed-time medians
   and dispersion, allocated words, retained graph and reuse from both inputs.
4. Interpretation: establish baseline variability before judging candidates;
   require no reproducible regression outside that noise on the agreed workload
   matrix, no new input-size prepass for disjoint union, and no new linear
   temporary allocation in the existing near-zero-allocation workloads. If a
   tradeoff is found, record it rather than declaring performance preserved.
   The current union profile measures allocation/sharing, not elapsed time or
   all of the cases above; extend the diagnostic coverage when implementing.
5. Integration: select the proved worker, remove the superseded directives,
   update the audits that currently require exactly four union overrides, and
   update this inventory and `SPECIFICATION.md` with residual assumptions.
   Keep the reference oracle. Close each item with theorem names, commands,
   toolchain, dated measurements and the exact claim now justified.

A target simulation can close a handwritten algorithm gap while retaining
compiler/runtime assumptions. An end-to-end claim additionally requires the
connections in milestone 3. Empirical replacement acceptance does not close N4.

## Evidence log

| Date | Completed work | Evidence and limits |
| --- | --- | --- |
| 2026-09-09 | Published the separate tracker and synchronized existing documents; organized local papers | Checked 64 local Markdown links/anchors across the eight documentation files; verified all four indexed PDF headers/end markers and SHA-256 digests; `git diff --check` passed. The Okasaki–Gill PDF was moved without changing its bytes; its origin is now identified as the 2015-04-17 Internet Archive capture of Andy Gill's ITTC author path, with the local checksum retained. These are documentation/artifact checks, not a rerun of the functional proof gate. |
| 2026-09-09 | V0.1–V0.3: source/extraction/proof audit, literature investigation and baseline profile | `rg -n '^Extract' PatriciaExtract.v`; inspection of native refinement and companion proofs, wrappers and generated OCaml; `sh check-ocaml-physical-equality.sh /opt/opam/4.14.3/.opam-switch/sources/ocaml-base-compiler.4.14.3`; `PATRICIA_UNION_PROFILE_SIZE=10000 make union-profile` passed. The latter rebuilt extraction/native profiling and checked results/sharing; it was not a fresh full proof/test run or a timing comparison. |
| 2026-09-09 | V1.1–V1.5: selected source-extracted direct union workers | `make union-proof`, `make extraction-boundary native-union-realizer-audit test union-oracle-native differential`, and `PATRICIA_UNION_PROFILE_SIZE=10000/100000 make union-profile` passed. The generated workers are direct recursive functions with erased `Acc`/equality evidence; at 100K, integer `Acc` allocation was 379/365/176/26/26 and string 100/81/26/26/26 words for disjoint/half-overlap/subset/equal/empty-right. These are allocation/sharing measurements on this toolchain, not timing, GC, compiler, or heap-refinement proofs. |
| 2026-09-09 | V2.1 cache-aware filtering gate | `make map-filter-profile` and `PATRICIA_MAP_FILTER_PROFILE_SIZE=100000 make map-filter-profile` passed after checking every result. Legacy, cached, and public paths respectively allocated 120,024/120,024/120,024 words for 10K keep-all, 60,024/60,024/60,024 for keep-even, and 31/31/31 for drop-all; at 100K they were 1,899,042/1,899,042/1,899,042, 949,514/949,514/949,514, and 31/31/31. Retained-word deltas differed only by small measurement noise. This is allocation evidence on OCaml 4.14.3 arm64/Linux, not a timing or cost proof. |
| 2026-09-10 | V2.2 bounded-prefix byte-scan refinement | Added `native_bounded_prefix_scan`, its complete-byte and terminal-tag helpers, guarded unsafe-access lemmas, and the complete-byte, terminal-tag and shorter-length-sentinel specifications. `native_bounded_prefix_scan_correct_from` proves the byte-range loop invariant; `native_bounded_prefix_scan_correct` proves equality with `agrees_before_bounded` for valid packed tags. `native_terminal_mask_equal_correct` proves all valid terminal `lxor`/left-shift/`land` masks by composing the finite one-difference-byte theorem with the XOR-code bridge, avoiding the rejected combined byte-pair/tag enumeration. `make all` passed with 480 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. This remains a source-model refinement, not a simulation of OCaml primitives or execution. |
| 2026-09-09 | V2.1 cache-aware deletion gate | `make remove-profile` and `PATRICIA_REMOVE_PROFILE_SIZE=100000 make remove-profile` passed after checking every result and the wrapper test checked absent-key root reuse. Legacy, cached, and public paths allocated 26/26/26 words for an absent key and 136/136/136 for the selected present key at 10K; at 100K they were 26/26/26 and 199/199/199. Retained-word deltas differed only by small measurement noise. This is allocation evidence on OCaml 4.14.3 arm64/Linux, not a timing or cost proof. |
| 2026-09-09 | V2.1 generated cached-consumer guard | `make cached-representative-audit` passed. It inspects extracted `remove_changed_cached`, `map_filter_cached`, `combine_fuel`, and `combine_structural`, requiring a cached constructor call and forbidding direct regular `branch`/`join` calls. This is a regression guard over generated syntax, not a semantic refinement proof. |
| 2026-09-09 | V2.1 closure of I5 | Removed the `StringPatricia.representative` extraction directive after migrating selected `Acc` union's three fallback joins to `join_cached`; `union_left_native_cached_disjoint_branches_correct_wf` supplies their source contract. `make all`, `make cached-representative-audit`, and 10K/100K `make union-profile` passed. At 100K the selected integer/string `Acc` allocation remains 379/365/176/26/26 and 100/81/26/26/26 words for disjoint/half/subset/equal/empty-right, with the same reported input sharing. The audit now rejects a representative directive. Allocation/sharing evidence is not a timing or cost proof. |
| 2026-09-10 | I9 public-wrapper inventory refresh | Counted 52 integer-wrapper and 43 string-wrapper implementation lines. Inspected both `.mli` files and `check_abstract_interfaces`, which tests key rejection/conversion, aliases, combine’s three callback cases and binary string keys through the public API. This establishes current scope and test coverage, not a semantic proof of the wrappers or the native-domain relation. |
| 2026-09-10 | V2.3 identity-shortcut source refinement | Added `native_string_same_sound`, `native_string_first_diff_with_identity`, and `native_string_first_diff_with_identity_refines`. The theorem proves the extracted first-difference worker’s successful `left == right` early return is semantically safe whenever a true physical test denotes equal source strings. `make all` passed with 481 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. This does not establish the OCaml physical-equality, string or indexed-loop semantics. |
| 2026-09-10 | V2.4 native-range inventory | Rechecked the 62-bit integer-routing closure, packed-token codec and standard mapping boundary. The end-marker at byte `length` with tag 8 makes `16 * length + 8 < 2^62` the exact retained string-capacity precondition; `native_packed_position_fits_string_capacity`, `native_byte_index_fits_string_capacity`, and `native_scan_successor_fits_string_capacity` prove conditional closure for valid tokens and scan counters. `make all` passed with 486 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. This is not proof that OCaml allocation, `String.length`, or `int` operations enforce the condition. |
| 2026-09-10 | V2.4 native `log2` loop model | Added `native_log2_loop` and `native_log2_loop_correct`: under the explicit `log2 value < fuel` precondition, repeated one-bit right shifts and accumulator increments equal `accumulator + log2 value`. `make all` passed with 487 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. This proves a source arithmetic invariant only; the handwritten OCaml loop, its bounded machine integers, and primitive/operator semantics remain I1/I8/I10 obligations. |
| 2026-09-10 | V2.4 fixed native-word `log2` fuel | Added `native_log2_loop_native_word_correct`, instantiating the loop invariant with 62 steps for every `fits_native_word` input (including zero). `make all` passed with 488 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. This closes only the source fuel calculation; proving that the target loop runs with the same arithmetic and bounds remains open. |
| 2026-09-10 | V2.4 XOR input to fixed `log2` fuel | Added `native_lxor_log2_fits_native_word` using `N.log2_lxor`, and `native_highest_differing_bit_loop_correct` to apply the 62-step source loop directly to bounded XOR operands. `make all` passed with 491 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. The OCaml `lxor`/`lsr` loop's target semantics and machine bounds remain open. |
| 2026-09-10 | V2.4 native routing shift counts | Added `native_routing_shift_count_fits`: a valid routing mask is below 62 and its prefix shift `mask + 1` is at most 62. `make all` passed with 492 declarations closed, extraction-boundary/native-union/cached-consumer audits, and all randomized/specialized/differential OCaml tests. The source range fact does not establish OCaml shift-count/operator behavior. |
| 2026-09-10 | V2.5 first-difference extraction experiment | Separately extracted the proved `native_string_first_diff` and added a temporary public-oracle comparison. Its generated worker destructed each native string through `String.sub s 1 (l - 1)`, implying repeated suffix copies; it also emitted an empty `String` unit that shadowed `Stdlib.String` during optimized compilation. The candidate edits and generated artifacts were removed/moved out of the backend; `make all` then passed again with the normal realizer. This rejects that extraction path on code shape before any performance claim. |

## Publications

### R1: Erased termination proofs

Xavier Leroy, *Well-founded recursion done right (Coq programming pearl)*,
CoqPL 2024. [Local PDF](papers/leroy-well-founded-recursion.pdf),
[author's PDF](https://xavierleroy.org/publi/wf-recursion.pdf).
Explicit accessibility-proof recursion is the basis for S1; its applicability
to this worker's extraction and performance remains to be tested.

### R2: Zoo

Clément Allain and Gabriel Scherer, *Zoo: A Framework for the Verification of
Concurrent OCaml 5 Programs using Separation Logic*, POPL 2026.
[Local PDF](papers/allain-scherer-2026-zoo.pdf),
[publication](https://doi.org/10.1145/3776701).
Relevant to S3 and the semantics of physical equality on immutable structures
containing mutable values. It is not a proof about this OCaml 4.14.3 binary.

### R3: Characteristic formulae

Arthur Charguéraud, *Program Verification Through Characteristic Formulae*,
ICFP 2010. [Author's PDF](https://www.chargueraud.org/research/2010/cfml/main.pdf).
Foundational method for verifying existing ML source; see also the
[current CFML project](https://github.com/charguer/cfml) for implementation scope.

### R4: Verified extraction

Yannick Forster, Matthieu Sozeau and Nicolas Tabareau, *Verified Extraction from
Coq to OCaml*, PLDI 2024.
[Local PDF](papers/forster-sozeau-tabareau-2024-verified-extraction.pdf),
[publication](https://doi.org/10.1145/3656379).
Relevant to S5's extraction boundary and interoperability obligations.

### R5: Cost reasoning

Armaël Guéneau, Arthur Charguéraud and François Pottier, *A Fistful of Dollars:
Formalizing Asymptotic Complexity Claims via Deductive Program Verification*,
ESOP 2018.
[Authors' PDF](https://chargueraud.org/research/2018/bigo_credits/bigo_credits.pdf).
Relevant if N4 is pursued; source-level cost reasoning still needs an explicit
connection to the native execution costs being claimed.

The [download index](papers/README.md) records provenance of the local PDFs.
Chris Okasaki and Andy Gill, *Fast Mergeable Integer Maps*, ACM SIGPLAN Workshop
on ML, pp. 77–86, September 1998:
[local PDF](papers/okasaki-gill-1998-fast-mergeable-integer-maps.pdf),
[publication record](https://ku-fpg.github.io/papers/Okasaki-98-IntMap/),
[archived author-path PDF](https://web.archive.org/web/20150417234429/https://ittc.ku.edu/~andygill/papers/IntMap98.pdf).
This provides algorithmic background, not verification of the present realizers.
