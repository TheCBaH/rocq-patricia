# Verified native string primitives: tracker

Last updated: 2026-09-12.

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

`PatriciaExtract.v` selects source-defined `NativeStringWorker` bodies for
all three string primitives: `packed_bit_at`, `first_diff_indexed_with_identity`
and `bounded_prefix_packed`. The scanners use erased `Acc` termination;
first difference shares one guarded byte XOR with its bounded mask scan, and
bounded prefix retains cached lengths and terminal-before-sentinel order.
Their source/codec refinements are kernel-checked. OCaml primitive execution,
the positive `(==)` contract, packed map-call-site representation, extraction,
compiler, runtime and measured-cost conclusions remain residual trust.

The frozen historical bodies are retained only as isolated benchmark fixtures.
The previous structural first-difference extraction remains rejected for suffix
copying and is not selected.

## S0 — Baseline and primitive interface

- [x] S0.1 Record the selected bodies, generated dependencies, compiler/Rocq
  versions, architecture and optimization configuration.
- [x] S0.2 Add candidate-versus-current primitive profiling alongside the
  existing correctness oracles. Batch operations and consume results; separate
  input creation from timed/allocation regions.
- [x] S0.3 Record repeated baseline timing variability and allocated words
  across the primitive and map workload matrix in the plan.
- [x] S0.4 Define the executable primitive interface and logical byte-string
  relation, including guarded reads, arithmetic bounds and positive-direction
  physical equality. Keep representation and bound evidence in `Prop`.
- [x] S0.5 Check a small extraction demonstrates direct native operations
  without runtime interface records, callback dispatch or string/list copying.
- [x] S0.6 Audit runtime string-capacity assumptions and all reachable native
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
- [x] S1.4 Run exhaustive byte/tag and out-of-range-index checks, differential
  tests and repeated routing/map timing comparisons.
- [x] S1.5 Select the candidate only after S4's integration obligations and
  S5's acceptance gates pass; document remaining assumptions.

Parent coverage: I2. Expected first executable replacement.

## S2 — Bounded prefix comparison

- [x] S2.1 Define the indexed Boolean worker with cached lengths and common
  sentinel, retaining terminal-before-sentinel branch ordering.
- [x] S2.2 Prove the index/access invariant and strict decrease of
  `min(split_byte, common) - byte`; recurse on erased `Acc` evidence.
- [x] S2.3 Prove equivalence to the sufficiently fuelled source scanner and
  compose `native_bounded_prefix_scan_correct`.
- [x] S2.4 Connect the terminal primitive mask expression through
  `native_terminal_mask_equal_correct`; cover tags 0 and 1 separately.
- [x] S2.5 Inspect generated code for a closed, fully applied tail-recursive
  loop without runtime fuel, state tuples, redundant per-byte bounds checks,
  list access, substring copying or first-difference options.
- [x] S2.6 Check empty/proper-prefix/equal inputs, sentinel/split coincidence,
  every valid tag, binary bytes and long prefixes against the oracle.
- [x] S2.7 Measure primitive timings and map combine/union allocation and
  timings; retain near-zero-allocation overlap/subset/equality behavior.
- [x] S2.8 Select only after S4/S5 pass and update parent I4/V2.2/V2.5 with
  the exact scope now established.

## S3 — Indexed first difference

- [x] S3.1 Define the indexed scan with cached lengths, a common-length
  sentinel, one XOR per scanned byte and absolute token construction.
- [x] S3.2 Prove prior-byte equality, access safety and termination using
  erased `Acc` evidence for `common - byte`.
- [x] S3.3 Define and prove the nonzero-XOR shifting-mask worker: higher bits
  already zero, `mask = 128 >> count`, termination within eight tests, valid
  shifts and result tag 1–8. Return an integer without an internal option.
- [x] S3.4 Prove indexed-worker refinement through
  `native_string_first_diff_refines` and existing byte-selection laws.
- [x] S3.5 Preserve and prove the identity shortcut using
  `native_string_same_sound`; keep its OCaml adequacy obligation explicit.
- [x] S3.6 Inspect extraction/compiler output for tail recursion, no copied
  suffixes, no runtime fuel and no per-byte result wrapping or allocation.
- [x] S3.7 Validate exhaustive one-byte pairs, proper prefixes, binary keys,
  long equal prefixes, same-object and separately allocated equal strings.
- [x] S3.8 Compare repeated primitive and map build/update timings and
  allocations, including fixed closure costs and the identity fast path.
- [x] S3.9 Select only after S4/S5 pass and update parent I3/V2.3/V2.5 with
  the exact refinement and residual contracts.

## S4 — Bindings and map representation

- [x] S4.1 Make the integration choice concrete: generated-worker bindings
  with explicit residual representation trust, or source-level parameterized
  map consumers with a proved native/logical representation relation.
- [x] S4.2 Establish valid-token production and ordered split consumption;
  compare logical `9*b+t` with packed `16*b+t`, not identical integers.
- [x] S4.3 Ensure proof-side packing/unpacking does not execute on hot paths.
- [x] S4.4 Retain the reference backend and abstract public interfaces; check
  module generation/linking for shadowed `String` units and accidental logical
  helper dependencies.
- [x] S4.5 Remove selected handwritten bodies only after their gates pass.
  If generated-worker aliases remain, inventory them and their exact trust
  status rather than claiming all substitution obligations disappeared.
- [x] S4.6 Add focused extraction-boundary guards for the final selected
  arrangement, without treating syntactic checks as semantic proofs.

## S5 — Common acceptance and documentation

Apply these gates to each selected worker, recording separate evidence rows.

- [x] S5.1 Compile proofs and inspect assumptions; record refinement theorem
  names and primitive/range hypotheses.
- [x] S5.2 Run `make all` and `make union-oracle-native`, plus candidate-specific
  exhaustive/differential checks. Investigate every failure.
- [x] S5.3 Record generated OCaml and relevant compiler-output findings for
  recursive arity, tail calls, closures, copying, fuel and allocations.
- [x] S5.4 Run repeated, interleaved current/candidate primitive and 10K/100K
  map workloads on the same toolchain; report medians, dispersion and words
  allocated. Use larger sizes when practical.
- [x] S5.5 Require no reproducible regression outside measured variability
  and no new allocation proportional to scanned bytes or map size in the
  existing constant-allocation paths. Record tradeoffs as failed gates.
- [x] S5.6 Update `patricia-bench.md`, the parent native inventory/tracker and
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
| 2026-09-12 | S1.5/S2.7--S2.8/S3.8--S3.9/S4.5/S5 selection | `PatriciaExtract.v` now binds `StringBits.bit_at` to `packed_bit_at`, `StringBits.first_diff` to `first_diff_indexed_with_identity`, and `StringBits.agrees_before_bounded` to `bounded_prefix_packed`; the former handwritten scanner bodies are removed. `packed_bit_at_refines_representation`, `bounded_prefix_scan_refines`, `bounded_prefix_packed_encode_refines`, `first_diff_indexed_refines`, `first_diff_indexed_spec`, `difference_tag_first_set_bit`, `first_diff_indexed_with_identity_refines`, `first_diff_indexed_valid`, and `encoded_position_order` supply the source/codec chain. The identity theorem retains `native_string_same_sound`; OCaml `(==)`, string/int/XOR/mask primitives, extraction/compiler/runtime execution and packed map-call-site representation are residual trust. |
| 2026-09-12 | S5.2/S5.3 final selected checks | After selecting all three bindings, `make all`, `make union-oracle-native`, and `make string-primitive-profile` passed. The all-suite assumption audit reports 542 declarations closed under the global context; randomized/oracle, specialized-union native, optimized/reference differential, exhaustive byte/tag and primitive-oracle checks passed. `check-native-string-workers.sh` confirmed direct packed access and scalar tail-recursive prefix/difference/tag workers with no structural strings, fuel, list access, copied suffixes, runtime proof arguments, or handwritten worker overrides. Native compiler inspection found tail branches for the scan/tag recursions and allocation sites only for final `Some` results. These checks do not prove target execution. |
| 2026-09-12 | S5.4/S5.5 interleaved acceptance | `PATRICIA_STRING_ROUNDS=5 PATRICIA_BENCH_SHORT_BATCH=8 make string-worker-performance` wrote `/tmp/patricia-string-acceptance.EjzGYB`: five interleaved samples for historical, each isolated worker, and all workers at 10K/100K, with arm64 Linux, OCaml 4.14.3, Flambda disabled, safe strings, GCC `-O2 -fno-strict-aliasing -fwrapv -pthread -fPIC -D_FILE_OFFSET_BITS=64`. Every run passed map equivalence. The all-workers rows had no timing range wholly above the normalized historical baseline and no median allocation increase; the isolated difference fixture had one 10K variable-key equal-union regression, recorded by the summarizer, but the actual selected all-workers arrangement did not reproduce it. At 100K fixed keys, selected build/lookup/membership were 10.105 ms/74.4/66.2 ns/op versus 9.973 ms/75.4/69.3 and allocated 6,082,676 versus 7,391,327 build words. At 100K variable keys, they were 17.564 ms/75.2/56.2 versus 17.526 ms/78.1/55.6 and 10,283,200 versus 11,578,414 words. Raw logs, source hashes and dispersion are reproducible through `benchmarks/README.md`; this is an empirical acceptance result for this configuration, not a portable cost claim. |
| 2026-09-12 | S2.3 indexed prefix refinement | `bounded_prefix_scan_acc_refines_fuel` proves equality to `native_bounded_prefix_scan` with fuel strictly above the remaining minimum-sentinel distance; `bounded_prefix_scan_refines` composes `native_bounded_prefix_scan_correct`. `bounded_prefix_packed_encode_refines` states the public correspondence through `encode_position`. `make NativeStringWorker.vo` passed. No primitive execution or map-call-site substitution theorem is claimed. |
| 2026-09-12 | S3.2/S3.4 indexed difference refinement | `first_diff_scan_acc_refines_fuel` discharges the erased-`Acc` bridge with both guarded length bounds; `first_diff_scan_fuel_cons` relates successor indexing to structural tails in proofs only; `first_diff_scan_fuel_refines` and `first_diff_indexed_refines` compose the native whole-string refinement. `first_diff_scan_acc_none_prior` and `first_diff_indexed_spec` establish previously scanned equality for `None` and the equal logical prefix before a produced split. `first_diff_indexed_with_identity_refines` retains the positive-direction identity hypothesis. `make NativeStringWorker.vo` passed. |
| 2026-09-12 | S3.3/S3.6 generated tag recursion | Removed the candidate's handwritten `native_byte_diff_tag` extraction loop. `difference_tag_acc` now recurses on erased `Acc (7-offset)` with `offset <= 7`; `difference_tag_acc_refines`, `difference_tag_refines`, `difference_tag_nonzero_range`, and `native_difference_bit_shift_mask` prove its bounded tag/mask behavior. `native_byte_xor_correct` connects the guarded shared XOR to byte equality and tag selection. Generated `first_diff_scan_acc` computes one XOR, and the two-argument tag loop allocates no options. `make extraction`, `make string-primitive-profile`, and `sh check-native-string-workers.sh` passed before the expanded performance series. |
| 2026-09-12 | S4.2 source codec integration | `first_diff_indexed_valid` proves every produced split has tag below 9. `encoded_position_order` proves logical strict order iff packed strict order; together with `packed_bit_at_encode_refines` and `bounded_prefix_packed_encode_refines`, this supplies valid production and ordered source consumption through the codec. The chosen generated-binding integration still trusts consistent packed representation at extracted map call sites. |
| 2026-09-11 | Initial plan and tracker | Based on inspection of the current extraction bodies, `StringBits.v`, `NativeRefinement.v`, union accessibility recursion, existing tests and project notes, plus primary-source extraction/verification references. No executable replacement or new performance measurement is claimed. |
| 2026-09-11 | S0.1 selected-body baseline | `PatriciaExtract.v` selects handwritten OCaml bodies for `StringBits.bit_at`, `StringBits.first_diff`, and `StringBits.agrees_before_bounded`; `make all` passed (492 declarations closed under the global context, extraction-boundary audits, randomized/oracle/differential tests). `make compiler-config` reported Rocq 9.2 built with OCaml 4.14.3; OCaml 4.14.3 native, arm64/aarch64 Linux 7.0.0-28-generic, 64-bit words, Flambda disabled, safe strings, and GCC `-O2 -fno-strict-aliasing -fwrapv -pthread -fPIC -D_FILE_OFFSET_BITS=64`. Generated dependencies are the optimized `extracted/StringBits.ml` and proof-aligned `reference_extracted/StringBits.ml`; wrappers bind the optimized extraction through `StringPatriciaInternal`. This records the current configuration, not runtime primitive correctness. |
| 2026-09-11 | S0.2 primitive baseline harness | Added `StringPrimitiveProfile.ml` and `make string-primitive-profile`. It pre-creates inputs, consumes results, takes seven samples after a warm-up, checks short binary/tag cases plus long workload endpoints against `PatriciaReference.StringBits`, and compares each candidate with the selected primitive. Timed inputs are created outside the timed/allocation region. |
| 2026-09-11 | S0.4 executable primitive contract | `NativeRefinement.v` defines `native_string_refines s bytes := bytes = native_bytes s`, with byte-length, guarded-access and byte-code-bound lemmas. Its packed-token capacity lemmas retain arithmetic/range premises in `Prop`; `native_string_same_sound` is the positive-direction physical-identity contract. `NativeStringWorker.v` exposes the selected packed worker through these source definitions. The corresponding OCaml length, integer, unsafe-access and `(==)` semantics remain named runtime assumptions rather than being asserted by the kernel. |
| 2026-09-11 | Current primitive baseline | `make string-primitive-profile`: seven-sample medians on the S0.1 toolchain were 3.015 ns/op and 24 words per 200K `bit_at` batch; 1.321 ns/op and 24 words per 100K same-object `first_diff`; 632.393 ns/op and 160,024 words per 20K separately allocated equal 1,024-byte pairs; 636.351 ns/op and 300,048 words per 20K late-different pairs; 1,149.094 and 1,150.703 ns/op with 24 words per 20K bounded late/proper-prefix scans. The 24-word readings are measurement overhead; the difference worker's option accounts for its extra fixed allocation. These primitive measurements do not cover the required repeated 10K/100K map matrix, so S0.3 and later acceptance gates remain open. |
| 2026-09-11 | S1.1/S1.2 source worker and proof | Added `NativeStringWorker.packed_bit_at`. Its source body decomposes a packed token, checks `byte < length` before the only unsafe read, returns true for tag 0, tests tags 1–8, and rejects 9–15. `packed_bit_at_refines_model` proves equality with `NativeRefinement.packed_bit_at`; `packed_bit_at_refines_representation` composes that result with `native_packed_bit_at_refines_representation`. The worker is bound to source `StringBits.bit_at` in `PatriciaExtract.v`; the binding crosses from logical source positions to packed runtime tokens, so map-level representation refinement is still an S4 obligation. |
| 2026-09-11 | S1.3 extraction and primitive check | `make extraction` generated `extracted/NativeStringWorker.ml` with only `lsr`, `land`, `<`, `=`, `<=`, `String.length`, one branch-guarded `String.unsafe_get`, and the byte shift/mask; helpers were extraction-inlined and the worker contains no recursion, options, records, or allocations. `make all`, `make union-oracle-native`, and `make string-primitive-profile` passed (the current all-suite assumption audit reports 517 closed declarations). The profile measured 3.185 ns/op (3.135–3.340) and 24 words per 200K batch for `bit_at`, where 24 words is measurement overhead. This is inspection and finite runtime evidence, not a proof of OCaml primitives. |
| 2026-09-11 | S0.2/S2 candidate harness | `StringPrimitiveProfile.ml` now differentially checks `NativeStringWorker.bounded_prefix_scan` against the current bounded primitive at every valid packed split in the short binary matrix and at each long-workload endpoint, in addition to the proof-aligned oracle checks. Inputs are created before timing and each result is consumed. This completes the reusable candidate-versus-current primitive harness; it does not substitute for the required map matrix. |
| 2026-09-11 | S2.1/S2.2 source loop | Added `bounded_prefix_scan_acc` and `bounded_prefix_scan` in `NativeStringWorker.v`. The loop caches both lengths and their minimum, tests the split terminal before the common sentinel, and carries `byte <= min(split_byte, common)` plus `Acc lt (min - byte)`. `bounded_prefix_scan_step` proves the next invariant and strict decrease; `bounded_prefix_scan_complete_read_safe` proves complete-byte reads lie below both lengths when common is their minimum; and `bounded_prefix_scan_acc_equation` exposes the erased-`Acc` branches for the remaining semantic induction. All this evidence is in `Prop` and erases. The candidate remains unbound pending its refinement theorem. |
| 2026-09-11 | S2.5 extraction/profile | `make extraction` produced a fully applied `let rec bounded_prefix_scan_acc` with separate scalar arguments, cached lengths/common, terminal/sentinel ordering, and no fuel, tuple state, substring, list access, or option result. The only byte read is the guarded native equality primitive; terminal comparison is the dedicated mask primitive. `make string-primitive-profile` checked the candidate and reported 857.556 ns/op (830.555–900.495) for late difference and 854.802 ns/op (826.347–862.193) for proper prefix, versus current 1,134.300 and 1,129.007 ns/op respectively; all batches reported the 24-word measurement overhead. These are one-machine primitive measurements, not S2/S5 selection evidence. |
| 2026-09-11 | S2.6 finite candidate validation | `make string-primitive-profile` exercises empty, same-object and separately allocated equal inputs, proper prefixes, late split/sentinel coincidence, NUL and non-ASCII binary strings, and long prefixes. For every ordered one-byte binary pair it checks all nine valid terminal tags (589,824 bounded candidate/current comparisons); compact cases also check the selected primitive against `PatriciaReference.StringBits`, and the long endpoints retain proof-aligned-oracle checks. The gate is finite validation only and does not replace S2.3's closed refinement proof. |
| 2026-09-11 | S2.4 terminal primitive proof | `native_ascii_prefix_equal_refines` connects the source terminal character scan to `native_prefix_code_equal`; `native_terminal_equal_refines` connects the guarded string terminal to `native_prefix_tag_equal`; and `native_terminal_mask_expression_refines` composes it with `native_terminal_mask_equal_correct` for tags 1–8. Tag 0 remains the separate continuation-marker true branch. The extraction realization is exactly the existing XOR/high-mask expression. |
| 2026-09-11 | S2.6 expanded differential matrix | `make string-primitive-profile` now checks all 65,536 ordered one-byte byte pairs at every valid tag 0–8 (589,824 candidate/current comparisons), as well as empty, embedded-NUL/non-ASCII short oracle cases, proper prefixes, independently allocated equality, sentinel cases, and long late-difference inputs. The compact/long cases still compare through the proof-aligned oracle; the exhaustive matrix uses the current primitive as the already-oracle-tested executable comparator to keep the structural oracle out of the timed benchmark path. S2.6 remains open until the candidate’s closed refinement theorem makes the whole matrix an oracle-backed validation. |
| 2026-09-11 | S0.3 repeated 10K/100K map baseline | Three interleaved `make benchmark` runs at each size (`PATRICIA_BENCH_STRING_LENGTHS=4`, variable maximum 4, five union samples) all completed with `Patricia comparison benchmark: ok`. At 10K, string build was 0.809–0.843 ms, lookup 68.7–74.7 ns/op, membership 64.5–66.5 ns/op, overlap union 67.219–69.462 us, subset 64.097–64.559 us, and equal 127.718–132.345 us; retained/allocated build words were invariant at 79,993/638,258 and union allocations 106/96/3/1 words for disjoint/overlap/subset/equal. At 100K those figures were 9.610–9.849 ms, 73.3–74.8 ns/op, 66.3–67.8 ns/op, 638.008–653.029 us, 611.067–681.877 us, and 1.181–1.270 ms; retained/allocated build words were 799,991/7,391,327 and union allocations 145/140/32/30 words. Disjoint union elapsed time remains below reliable resolution (0.954–3.099 us), but its allocation is stable. Detailed reproduction is in `patricia-bench.md`. |
| 2026-09-11 | S0.5 extraction shape | `make extraction` emits `NativeStringWorker.packed_bit_at` and `bounded_prefix_scan_acc` as direct OCaml functions with inlined native integer/string operations. Inspection found no runtime interface record, callback dispatch, list conversion, substring copy, or runtime termination proof; the worker profile reports only fixed measurement overhead. This establishes viable shape for the workers, not target-level primitive semantics. |
| 2026-09-11 | S1.4 executable validation | `PatriciaTest.ml` exhausts all 256×256 one-byte pairs, tests every packed tag 0–15, and queries byte indices through `length + 2`; tags 9–15 and past-end positions must return false. `make all` runs that suite and the optimized/reference differential backend test. The repeated 10K/100K map series in the S0.3 row exercises routing, builds, lookup, membership, updates, combine, and union with the selected source-defined `bit_at` binding. This is finite target execution evidence only; the primitive/runtime correspondence remains an explicit S4/S5 trust boundary. |
| 2026-09-11 | S0.6 capacity/arithmetic audit | On this OCaml 4.14.3 arm64 runtime, `Sys.max_string_length` reports 144,115,188,075,855,863 and `max_int` 4,611,686,018,427,387,903. The packed end-token expression is 2,305,843,009,213,693,816 (`16 * max_string_length + 8`), strictly below `max_int`, so the conditional `native_string_packed_capacity` source closure covers the documented runtime maximum. The selected/candidate workers additionally use only byte shift 4, tag mask 15, data offsets 0–7, and terminal shift counts 1–8; `NativeRefinement.v` carries the conditional word/index/successor and terminal-mask range lemmas. This is an audit of the installed runtime’s advertised limit and source arithmetic, not a proof that allocation, OCaml primitives, compiler lowering, or all future runtimes satisfy those contracts. |
| 2026-09-11 | S3.1 indexed candidate | Added `first_diff_scan_acc`/`first_diff_indexed` in `NativeStringWorker.v`. The source loop caches both lengths and their minimum, carries erased `Acc lt (common - byte)`, performs one native byte-XOR-zero test each iteration, emits `16 * byte + tag` only at the terminal, and returns the shorter-key marker at the common sentinel. Extraction yields a closed tail-recursive loop with cached scalar state. `make string-primitive-profile` differentially checked it against the selected primitive and reported 558.746 ns/op for equal copies (24-word measurement overhead) and 556.302 ns/op for a late difference (140,024 words per 20K, including `Some` results); it remains unbound pending tag/outer refinement proofs and identity handling. |
| 2026-09-11 | S3.6 extraction inspection | `extracted/NativeStringWorker.ml` contains a fully applied tail-recursive `first_diff_scan_acc` with scalar cached state and no source fuel, suffix/string copying, list access, or per-byte `option`. It runs one XOR-zero test per scanned byte and allocates only the final `Some`; the bounded eight-test tag helper is entered only after a mismatch. `first_diff_indexed_with_identity` adds the separately profiled fast path. These code-shape results do not by themselves establish selection. |
| 2026-09-11 | S3.5 identity fast path | Added `first_diff_indexed_with_identity`; its source `native_string_same` defaults false and extracts to OCaml `(==)`. `first_diff_indexed_identity_shortcut` proves that a positive result under `native_string_same_sound` entails equal source strings and returns `None`. The profile differentially checks the wrapper and measured same-object calls at 1.750 ns/op (1.719–2.019) with 24 words of batch measurement overhead. The positive-direction `(==)` adequacy contract is retained explicitly; no claim is made for a false result or for compiler/heap semantics. |
| 2026-09-11 | S3.7 candidate validation | The primitive harness now checks the identity wrapper for every ordered one-byte pair (65,536 comparisons), along with the existing proper-prefix, NUL/non-ASCII binary, long equal-prefix, same-object, and separately allocated equal-string matrices. Each candidate result is compared to the selected primitive; compact and long cases also retain proof-aligned-oracle checks. `make string-primitive-profile` passed this full matrix. This finite differential evidence is distinct from S3.4’s required closed refinement proof. |
| 2026-09-12 | S3.3 total XOR tag worker | Replaced the source `native_xor_diff_tag` option wrapper with `native_xor_diff_tag_from 8 0`: a bounded total loop over `NativeRefinement.native_byte_bit`, whose definition is the XOR/mask test at `2^(7-offset)`. `native_xor_diff_tag_from_some` proves agreement with the corresponding leading-zero loop, and `native_xor_diff_tag_some`/`native_xor_diff_tag_range` prove the nonzero-byte result is exactly `1 + offset` and lies in 1–8. The existing `native_byte_bit_is_ascii_xor_bit` and leading-zero proofs supply the higher-bit, shift and mask invariant. The extraction maps the byte helper to the matching direct OCaml XOR/right-shift loop with no option. |
| 2026-09-12 | S3.2 scan-invariant foundation | Added `first_diff_scan_complete_read_safe`: a non-sentinel iteration has both cached-length bounds before either byte is read. `native_byte_difference_zero_complete` proves the guarded XOR-zero test is exactly equality of the two fetched characters, while `first_diff_scan_step` supplies the erased-`Acc` successor/decrease fact. The non-extracted `first_diff_scan_fuel` companion and `first_diff_scan_fuel_none_prior` now prove by structural induction that a `None` scan result has equal bytes at every previously scanned index. The remaining task is the extensional bridge from this fuelled semantics to the branch-indexed erased-`Acc` worker, then the outer refinement; S3.2 remains open. |
| 2026-09-11 | S4.1/S4.3 binding decision | The selected `StringBits.bit_at` extraction is explicitly a generated-worker binding to `NativeStringWorker.packed_bit_at`, rather than ordinary extraction of the logical-position API. The residual trust is the logical `9*b+t` to packed `16*b+t` representation correspondence at map call sites and the OCaml primitive contracts. The worker’s generated code performs only packed operations; proof-side codec conversion is absent from its hot loop. The unbound prefix/difference workers do not change this selected arrangement. |
| 2026-09-12 | S4.4/S4.6 boundary audit | The reference extraction remains separately packed as `PatriciaReference`, and `make differential` links it beside the optimized backend while public wrappers retain abstract map types. `check-native-string-workers.sh`/`make native-string-worker-audit` requires the `StringBits.bit_at` worker binding, direct guarded native access, and rejects generated structural `String.get`/`String.sub`, `open String`, and source tag-scan dependencies. It now also requires the candidate `first_diff_scan_acc` recursion and rejects the proof-only `first_diff_scan_fuel` from generated output. The guard passed after `make extraction`; it is syntactic boundary evidence, not a semantic proof. |
| 2026-09-11 | S5.1--S5.3 selected `bit_at` acceptance | `make all` compiled the proof suite and reported 517 declarations closed under the global context. The selected worker’s source theorems are `packed_bit_at_refines_model`, `packed_bit_at_encode_refines`, and `packed_bit_at_refines_representation`; their explicit hypotheses cover the native string representation, guarded byte range, token encoding and runtime capacity boundary. `make all`, `make union-oracle-native`, `./patricia-differential-test`, `./patricia-union-native-test`, and `make string-primitive-profile` all passed. The latter measured selected `bit_at` at a 3.101 ns/op median (3.060--3.179, 24 batch-overhead words per 200K operations). The generated-worker audit confirmed a direct packed worker with guarded `Stdlib.String.unsafe_get`, no structural string operation, recursion, records, options or allocation. These completed acceptance rows apply only to the selected `bit_at` binding: the prefix and first-difference candidates remain unselected and their open semantic/integration gates are not waived. |

For each implementation result add: task ID, theorem names, exact commands,
toolchain/machine, workloads, timing distribution, allocation measurements,
selection decision and residual assumptions. Link detailed results rather
than duplicating benchmark tables here.
