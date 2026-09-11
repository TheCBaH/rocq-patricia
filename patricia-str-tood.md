# Verified native string primitives: tracker

Last updated: 2026-09-11.

This tracker owns detailed implementation tasks for
[patricia-str-plan.md](patricia-str-plan.md). The filename `patricia-str-tood.md`
is intentional. The parent inventory and V2 milestones remain in
[patricia-native-verification.md](patricia-native-verification.md); project
decisions remain in [patricia-todo.md](patricia-todo.md).

`[x]` means complete with recorded evidence, `[ ]` means open, and `[-]` means
deferred. Proposed theorem and module names are not existing declarations.
Do not mark an implementation complete on the strength of a source model,
generated-code inspection or allocation measurement alone.

## Current status

The three handwritten bodies remain selected in `PatriciaExtract.v`.
The packed `bit_at` binding now selects a source-defined worker whose native
operations are limited to length, token shifts/masks, guarded byte access and
the byte bit test. Its source refinement is kernel-checked, while the OCaml
primitive and packed-binding correspondence remain explicit residual trust.
`first_diff` and `agrees_before_bounded` are still handwritten extraction
bodies. A reproducible native harness measures the selected binding against
the proof-aligned extraction as an oracle; no worker is selected until its
full S4/S5 gates pass. The earlier structural first-difference extraction was
rejected for suffix copying; it is not a candidate to reinstate unchanged.

## S0 — Baseline and primitive interface

- [x] S0.1 Record the selected bodies, generated dependencies, compiler/Rocq
  versions, architecture and optimization configuration.
- [ ] S0.2 Add candidate-versus-current primitive profiling alongside the
  existing correctness oracles. Batch operations and consume results; separate
  input creation from timed/allocation regions.
- [ ] S0.3 Record repeated baseline timing variability and allocated words
  across the primitive and map workload matrix in the plan.
- [ ] S0.4 Define the executable primitive interface and logical byte-string
  relation, including guarded reads, arithmetic bounds and positive-direction
  physical equality. Keep representation and bound evidence in `Prop`.
- [ ] S0.5 Check a small extraction demonstrates direct native operations
  without runtime interface records, callback dispatch or string/list copying.
- [ ] S0.6 Audit runtime string-capacity assumptions and all reachable native
  arithmetic; separate conditional source closure from runtime adequacy.

Exit gate: a reviewable primitive contract, reproducible baseline and viable
extraction shape. Parent coverage: I8 and V2.4/V2.5, conditionally and only for
the string workers.

## S1 — Packed bit access

- [x] S1.1 Define a source worker using native token shifts/masks and guarded
  indexed byte access, preserving marker and invalid-tag behavior.
- [x] S1.2 Prove its bit test and decoding agree with the existing packed
  model; compose `native_packed_bit_at_refines_representation` with the codec.
- [x] S1.3 Inspect extraction/compiler output for constant-time access,
  correct guard ordering and no allocation.
- [ ] S1.4 Run exhaustive byte/tag and out-of-range-index checks, differential
  tests and repeated routing/map timing comparisons.
- [ ] S1.5 Select the candidate only after S4's integration obligations and
  S5's acceptance gates pass; document remaining assumptions.

Parent coverage: I2. Expected first executable replacement.

## S2 — Bounded prefix comparison

- [ ] S2.1 Define the indexed Boolean worker with cached lengths and common
  sentinel, retaining terminal-before-sentinel branch ordering.
- [ ] S2.2 Prove the index/access invariant and strict decrease of
  `min(split_byte, common) - byte`; recurse on erased `Acc` evidence.
- [ ] S2.3 Prove equivalence to the sufficiently fuelled source scanner and
  compose `native_bounded_prefix_scan_correct`.
- [ ] S2.4 Connect the terminal primitive mask expression through
  `native_terminal_mask_equal_correct`; cover tags 0 and 1 separately.
- [ ] S2.5 Inspect generated code for a closed, fully applied tail-recursive
  loop without runtime fuel, state tuples, redundant per-byte bounds checks,
  list access, substring copying or first-difference options.
- [ ] S2.6 Check empty/proper-prefix/equal inputs, sentinel/split coincidence,
  every valid tag, binary bytes and long prefixes against the oracle.
- [ ] S2.7 Measure primitive timings and map combine/union allocation and
  timings; retain near-zero-allocation overlap/subset/equality behavior.
- [ ] S2.8 Select only after S4/S5 pass and update parent I4/V2.2/V2.5 with
  the exact scope now established.

## S3 — Indexed first difference

- [ ] S3.1 Define the indexed scan with cached lengths, a common-length
  sentinel, one XOR per scanned byte and absolute token construction.
- [ ] S3.2 Prove prior-byte equality, access safety and termination using
  erased `Acc` evidence for `common - byte`.
- [ ] S3.3 Define and prove the nonzero-XOR shifting-mask worker: higher bits
  already zero, `mask = 128 >> count`, termination within eight tests, valid
  shifts and result tag 1–8. Return an integer without an internal option.
- [ ] S3.4 Prove indexed-worker refinement through
  `native_string_first_diff_refines` and existing byte-selection laws.
- [ ] S3.5 Preserve and prove the identity shortcut using
  `native_string_same_sound`; keep its OCaml adequacy obligation explicit.
- [ ] S3.6 Inspect extraction/compiler output for tail recursion, no copied
  suffixes, no runtime fuel and no per-byte result wrapping or allocation.
- [ ] S3.7 Validate exhaustive one-byte pairs, proper prefixes, binary keys,
  long equal prefixes, same-object and separately allocated equal strings.
- [ ] S3.8 Compare repeated primitive and map build/update timings and
  allocations, including fixed closure costs and the identity fast path.
- [ ] S3.9 Select only after S4/S5 pass and update parent I3/V2.3/V2.5 with
  the exact refinement and residual contracts.

## S4 — Bindings and map representation

- [ ] S4.1 Make the integration choice concrete: generated-worker bindings
  with explicit residual representation trust, or source-level parameterized
  map consumers with a proved native/logical representation relation.
- [ ] S4.2 Establish valid-token production and ordered split consumption;
  compare logical `9*b+t` with packed `16*b+t`, not identical integers.
- [ ] S4.3 Ensure proof-side packing/unpacking does not execute on hot paths.
- [ ] S4.4 Retain the reference backend and abstract public interfaces; check
  module generation/linking for shadowed `String` units and accidental logical
  helper dependencies.
- [ ] S4.5 Remove selected handwritten bodies only after their gates pass.
  If generated-worker aliases remain, inventory them and their exact trust
  status rather than claiming all substitution obligations disappeared.
- [ ] S4.6 Add focused extraction-boundary guards for the final selected
  arrangement, without treating syntactic checks as semantic proofs.

## S5 — Common acceptance and documentation

Apply these gates to each selected worker, recording separate evidence rows.

- [ ] S5.1 Compile proofs and inspect assumptions; record refinement theorem
  names and primitive/range hypotheses.
- [ ] S5.2 Run `make all` and `make union-oracle-native`, plus candidate-specific
  exhaustive/differential checks. Investigate every failure.
- [ ] S5.3 Record generated OCaml and relevant compiler-output findings for
  recursive arity, tail calls, closures, copying, fuel and allocations.
- [ ] S5.4 Run repeated, interleaved current/candidate primitive and 10K/100K
  map workloads on the same toolchain; report medians, dispersion and words
  allocated. Use larger sizes when practical.
- [ ] S5.5 Require no reproducible regression outside measured variability
  and no new allocation proportional to scanned bytes or map size in the
  existing constant-allocation paths. Record tradeoffs as failed gates.
- [ ] S5.6 Update `patricia-bench.md`, the parent native inventory/tracker and
  `SPECIFICATION.md` as appropriate. Distinguish proved algorithms, trusted
  primitive execution and empirical performance. Check Markdown links and
  `git diff --check`.

## Deferred alternatives

- [-] A1 Investigate primitive `PString` only after resolving its installed
  length limit and indexed-access overhead without narrowing the public domain.
- [-] A2 If extraction shape fails, assess verification of the actual OCaml
  bodies with CFML or another suitable target semantics; establish toolchain
  and primitive support before claiming target-level evidence.
- [-] A3 Investigate verified extraction/alternative compiler optimization
  separately, with explicit transformation and downstream trust boundaries.
- [-] A4 Formal cost, allocation and GC proofs remain project milestone N4.

## Evidence log

| Date | Item | Evidence and limits |
| --- | --- | --- |
| 2026-09-11 | Initial plan and tracker | Based on inspection of the current extraction bodies, `StringBits.v`, `NativeRefinement.v`, union accessibility recursion, existing tests and project notes, plus primary-source extraction/verification references. No executable replacement or new performance measurement is claimed. |
| 2026-09-11 | S0.1 selected-body baseline | `PatriciaExtract.v` selects handwritten OCaml bodies for `StringBits.bit_at`, `StringBits.first_diff`, and `StringBits.agrees_before_bounded`; `make all` passed (492 declarations closed under the global context, extraction-boundary audits, randomized/oracle/differential tests). `make compiler-config` reported Rocq 9.2 built with OCaml 4.14.3; OCaml 4.14.3 native, arm64/aarch64 Linux 7.0.0-28-generic, 64-bit words, Flambda disabled, safe strings, and GCC `-O2 -fno-strict-aliasing -fwrapv -pthread -fPIC -D_FILE_OFFSET_BITS=64`. Generated dependencies are the optimized `extracted/StringBits.ml` and proof-aligned `reference_extracted/StringBits.ml`; wrappers bind the optimized extraction through `StringPatriciaInternal`. This records the current configuration, not runtime primitive correctness. |
| 2026-09-11 | S0.2 primitive baseline harness | Added `StringPrimitiveProfile.ml` and `make string-primitive-profile`. It pre-creates inputs, consumes results, takes seven samples after a warm-up, and checks short binary/tag cases plus long workload endpoints against `PatriciaReference.StringBits`. A future candidate can be added without changing the generator or oracle. It currently measures only the selected body, so S0.2 remains open until a candidate-versus-current comparison exists. |
| 2026-09-11 | Current primitive baseline | `make string-primitive-profile`: seven-sample medians on the S0.1 toolchain were 3.015 ns/op and 24 words per 200K `bit_at` batch; 1.321 ns/op and 24 words per 100K same-object `first_diff`; 632.393 ns/op and 160,024 words per 20K separately allocated equal 1,024-byte pairs; 636.351 ns/op and 300,048 words per 20K late-different pairs; 1,149.094 and 1,150.703 ns/op with 24 words per 20K bounded late/proper-prefix scans. The 24-word readings are measurement overhead; the difference worker's option accounts for its extra fixed allocation. These primitive measurements do not cover the required repeated 10K/100K map matrix, so S0.3 and later acceptance gates remain open. |
| 2026-09-11 | S1.1/S1.2 source worker and proof | Added `NativeStringWorker.packed_bit_at`. Its source body decomposes a packed token, checks `byte < length` before the only unsafe read, returns true for tag 0, tests tags 1–8, and rejects 9–15. `packed_bit_at_refines_model` proves equality with `NativeRefinement.packed_bit_at`; `packed_bit_at_refines_representation` composes that result with `native_packed_bit_at_refines_representation`. The worker is bound to source `StringBits.bit_at` in `PatriciaExtract.v`; the binding crosses from logical source positions to packed runtime tokens, so map-level representation refinement is still an S4 obligation. |
| 2026-09-11 | S1.3 extraction and primitive check | `make extraction` generated `extracted/NativeStringWorker.ml` with only `lsr`, `land`, `<`, `=`, `<=`, `String.length`, one branch-guarded `String.unsafe_get`, and the byte shift/mask; helpers were extraction-inlined and the worker contains no recursion, options, records, or allocations. `make all`, `make union-oracle-native`, and `make string-primitive-profile` passed (the all-suite assumption audit reports 496 closed declarations). The profile measured 3.185 ns/op (3.135–3.340) and 24 words per 200K batch for `bit_at`, where 24 words is measurement overhead. This is inspection and finite runtime evidence, not a proof of OCaml primitives or an S5 selection result. |

For each implementation result add: task ID, theorem names, exact commands,
toolchain/machine, workloads, timing distribution, allocation measurements,
selection decision and residual assumptions. Link detailed results rather
than duplicating benchmark tables here.
