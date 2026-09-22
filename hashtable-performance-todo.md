# Generated HAMT performance tracker

Last updated: 2026-09-22.
Contract and acceptance: [implementation plan](hashtable-performance-plan.md).
Measurements: [performance note](hashtable-performance.md).
This tracker is separate from [H0–H5](hashtable-todo.md) and Patricia work.

`[x]` means completed with evidence; `[ ]` means open. Proposed filenames,
theorem descriptions and targets are not implementation evidence. Close tasks
with revision/source/theorem references, command, result and date. Record
foreign obligations separately from kernel-checked source statements.

## Current decision

Feasible: proceed with benchmark correction, bounded scalar realization and
direct native workers before considering storage changes. Documentation and
baseline inspection are complete. No performance optimization has been
implemented or validated, and no new performance target is achieved.

| Gate | Depends on | Status / closure condition |
| --- | --- | --- |
| HP0 — corrected baseline | Review | Open: reproducible isolated timings, retention modes and attribution |
| HP1 — scalar realization | HP0 | Open: model/range proofs, target inventory, primitive tests and stage measurements |
| HP2 — sequence hot path | HP1 | Open: no child-list emptiness conversion, refinement and persistence tests |
| HP3 — direct workers | HP2 | Open: no public hot-path source round trip or collision-list conversion |
| HP4 — specialization decision | HP3 + residual profile | Pending: implement only justified candidates, or explicitly defer |
| HP5 — release evidence | HP1–HP3 + HP4 decision | Open: aggregate checks, matched matrix, boundary documentation and clean build |

## Review and baseline evidence

- [x] **R1** Inspect scalar extraction, sequence use and source fallback paths;
  compare `PatriciaExtract.v` and its native verification inventory.
- [x] **R2** Correct benchmark/retention descriptions and distinguish generated
  audits from the standalone backend audit.
- [x] **R3** Regenerate and rerun the original integer/string benchmark targets;
  confirm reported build-allocation baseline on the local pinned toolchain.
- [x] **R4** Write staged implementation plan, primitive contracts, proof/runtime
  implications, verification matrix and measurable acceptance targets.

## Implementation checklist

- [ ] **HP0.1** Move oracle work/input-value creation outside timing; consume and
  validate measured results; separate repeated-set build and first-wins `of_list`.
- [ ] **HP0.2** Add latest-root/all-prefix timed policies and controlled live-heap
  measurement with all roots alive; separate mutable single-version results.
- [ ] **HP0.3** Add matched Patricia/AVL/Hashtbl/HAMT integer/string distributions,
  sizes, seeds, repetitions and machine-readable environment/revision metadata.
- [ ] **HP0.4** Profile scalar operations, conversions, primitive copies and
  hashing, or record controlled microbenchmark attribution and its limitations.
- [ ] **HP0.G** Publish corrected baseline and remaining attribution uncertainty.

- [ ] **HP1.1** Define bounded scalar wrappers and source popcount; prove
  equivalence to `HashTableBits` and range closure for reachable calls.
- [ ] **HP1.2** Add small OCaml scalar realizers/extraction bindings, platform
  guard and complete primitive/foreign-obligation inventory.
- [ ] **HP1.3** Register new modules in proof, assumption audit, extraction,
  bytecode/native link recipes and clean rules.
- [ ] **HP1.4** Add model-vs-target scalar tests across slot/hash/bitmap/depth
  boundaries, full 16-bit popcount corpus and random 32-bit patterns.
- [ ] **HP1.G** Proof/audit/test pass; generated arithmetic inspection and isolated
  scalar-stage measurements recorded against HP0.

- [ ] **HP2.1** Add proved sequence emptiness and its array contract/binding;
  replace deletion's child-view check and reprove refinement.
- [ ] **HP2.2** Reuse computed dense ranks through private helpers, preserving
  insertion versus existing-child bounds.
- [ ] **HP2.3** Record bounded/option-free indexing decision from profile; keep
  checked indexing unless new call-site proof and measurable benefit justify it.
- [ ] **HP2.G** Generated deletion has no child-list emptiness conversion;
  persistence and operation tests pass; stage measurements recorded.

- [ ] **HP3.1** Implement/prove direct native empty/leaf/join workers; preserve
  total model fallback behavior or prove a separate valid-public-worker bridge.
  Partial: `native_set` and `native_remove` now handle empty and leaf cases
  directly; distinct-hash leaf joins and collision cases still use the
  source-model conversion.
- [ ] **HP3.2** Implement/prove indexed sequence collision workers, termination,
  representative retention and empty/singleton normalization; test buckets >32.
  Prerequisite complete: the private sequence contract now exposes a refined
  length operation, extracted as `Array.length`, for bounded indexed workers.
- [ ] **HP3.3** Lift worker proofs to native public validity/lookup/set/remove/
  first-wins loading; preserve seed, callback and arbitrary-payload contracts.
- [ ] **HP3.4** Separate proof/test conversions from public operation paths and
  record enumeration strategy and its measured allocation.
- [ ] **HP3.G** Generated public get/mem/set/remove/of_list paths avoid source
  round trips and sequence-to-list conversion; full semantic matrix passes.

- [ ] **HP4.D** Record residual profile and explicit implement/defer decision.
- [ ] **HP4.G** If selected, each sequence/layout/changed-result experiment has
  model proof, target contract, audit, persistence tests and isolated results;
  otherwise record why the stage is deferred.

- [ ] **HP5.1** Strengthen generated public-call-path and extraction-binding
  audits, add negative fixtures, replace obsolete required-fallback checks.
- [ ] **HP5.2** Run `make hashtable-proof hashtable-assumptions`, `make hashtable`,
  `make all`, `make hashtable-benchmark-smoke`; integrate proposed new checks.
- [ ] **HP5.3** Run clean-checkout aggregate and matched repeated performance
  matrix; record achieved/unmet targets and any repeatable regressions.
- [ ] **HP5.4** Update README, performance note and release/foreign-contract
  inventories; retain source proof versus target testing distinction.
- [ ] **HP5.G** Publish final local decision with proof/test/measurement evidence.
- [ ] **CI** Record hosted CI result separately; local success is not hosted CI.

## Validation log

| Date | Scope | Command / evidence | Result |
| --- | --- | --- | --- |
| 2026-09-22 | R1/R2 | Read `HashTableNative.v`, `HashTableBits.v`, array extraction/refinement, both benchmark sources, backend audits, `PatriciaExtract.v` and Patricia verification inventory | Confirmed recursive extracted scalar operations, deletion/collision/source conversion paths, and benchmark/audit limitations; attribution remains open. |
| 2026-09-22 | R3 | `make hashtable-benchmark hashtable-string-benchmark`; Rocq 9.2 / OCaml 4.14.3 via Makefile tool paths | Both regenerated checked workloads passed at 2,000 bindings, seed 31. Public/standalone build bytes: integer 215,905,264/1,394,040; string 243,088,456/1,279,488. Single-run times: integer 8.056/0.302 ms; string 9.190/0.360 ms. Not an optimized result. |
| 2026-09-22 | R4 | `hashtable-performance-plan.md` and this tracker | Feasibility, dependency order, source/foreign contracts and acceptance criteria documented; all implementation gates remain open. |
| 2026-09-22 | Review validation | `check-hashtable-native-array-extraction.sh`, `check-hashtable-native-array-backend.sh`, `check-hashtable-primitives.sh`; `git diff --check`, new-file whitespace checks and local Markdown link existence checks | All passed. Existing audits permit the identified generated hot-path conversions; passing them does not establish HP3/HP5. Runtime/proof sources were not changed; the full proof/test aggregate was not rerun for this documentation task. |
| 2026-09-22 | HP0.1/HP0.2 (integer, partial) | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=2 make hashtable-benchmark` | Passed. `HashTableBenchmark.ml` now precomputes bindings, values, query sets and expected checks outside timing; separately times first-wins `of_list`, repeated `set`, hit/miss lookup and membership, existing/new update, present/missing removal and enumeration; retains each timed result through an observable checksum and validates it afterward. It also reports latest-root and all-prefix post-GC live heap. `HashTableBenchmarkSupport` rotates task order, takes configurable warmups/repetitions (defaults: 1/7), and saves raw/summary JSONL records with revision/dirty-state env fields, host, OCaml, word-size and GC configuration. String/matched-Patricia distributions, profiler attribution and the HP0 baseline gate remain open. |
| 2026-09-22 | HP0.1 (fixed-width string, partial) | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=2 make hashtable-string-benchmark` | Passed. The string harness now uses the same warmup/repetition, allocation, JSONL-metadata and observable-result boundary as the integer harness. Timed lookup now computes only a checksum; the independent lookup oracle runs after timing. Mutable update/removal trials copy their prepared table, so repeated samples do not mutate the next sample's input. Operation/distribution expansion, latest-root string retention, matched Patricia and attribution remain open. |
| 2026-09-22 | HP0.2/HP0.3 (string distributions, partial) | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_STRING_PATTERN=common-prefix make hashtable-string-benchmark` | Passed. The harness accepts `fixed-width`, `mixed-length`, and `common-prefix` (192-byte prefix) deterministic byte-string inputs, labels JSONL records with the chosen distribution, and now separately measures latest-root and all-prefix live heap for every persistent implementation. The smoke target pins fixed-width. Matched Patricia inputs, repeated full matrix, miss/membership/enumeration string operations, and profiler attribution remain open. |
| 2026-09-22 | HP1.1–HP1.4 (lookup-routing scalar slice) | `make hashtable-proof hashtable-native-array-extraction-audit hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-scalar-test`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. `HashTableNativeBits.v` defines transparent scalar wrappers with closed equality lemmas; generated `native_get` now reaches checked 64-bit OCaml chunk, bitmap-membership and rank realizers. The adapter is tested across every slot, all 16-bit bitmap words, 10,000 deterministic 32-bit masks, bitmap extremes, hashes 0/`2^30-1`, and depths 0–6. The extraction audit requires these bindings and scalar routing in `native_get`; bytecode/native model tests passed. Before the following set-routing change, the 100-binding smoke measured public lookup-hit allocation at 113,952 bytes (previous corrected smoke: 3,260,640). Range closure at the public API, scalar routing for removal, complete aggregate links, stage measurement matrix and all HP1 closure conditions remain open. |
| 2026-09-22 | HP1.1–HP1.4 (set-routing scalar slice) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test-native hashtable-scalar-test`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. Generated `native_set` now uses the same source-defined chunk, bitmap-membership and rank wrappers; its existing source refinement proof closes after explicit conversion between the transparent wrapper and model forms. The extraction audit requires both public get and set workers to contain scalar routing. The smoke measured public `of_list` build / existing set / new set allocation at 2,208,888 / 2,404,136 / 2,734,800 bytes, down from the prior corrected 100-binding smoke's 5,761,848 / 8,697,512 / 8,600,112. Removal and source-join fallback scalar work remain open; no stage gate is closed. |
| 2026-09-22 | HP1.1–HP1.4 (remove-routing scalar slice) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. Generated `native_remove` now uses bounded scalar chunk, membership and rank routing while retaining the established source-model bitmap-edit helpers. Its existing refinement theorem closes with transparent wrapper conversions. The audit now requires all three public get/set/remove workers to route through the scalar chunk binding. The 100-binding smoke measured public present/missing removal allocation at 2,650,952 / 1,550,736 bytes, down from 5,797,320 / 7,191,632 before scalar routing. Join/source-fallback arithmetic, range-closure theorems, full matrix and HP1 gate remain open. |
| 2026-09-22 | HP1.1–HP1.4 (branch bitmap/edit scalar slice) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit hashtable-scalar-test` | Passed. Native branch replace/insert/remove now call scalar dense-rank and bitmap insert/delete wrappers, with the existing refinement proofs closing by transparency. Generated source contains scalar rank at branch edits and scalar insert/delete bindings; the audit requires all five approved scalar operations. Source-join fallback arithmetic, range closure, full aggregate and stage matrix remain open. |
| 2026-09-22 | HP2.1 (sequence emptiness) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableArrayRefinement.v`; `make hashtable-native-primitives-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `pseq_is_empty` has a source view theorem; `array_sequence_contract` now requires and refines an emptiness operation. `native_children_remove` calls it instead of materializing the child view. The array adapter realizes it with `Array.length = 0`; primitive tests cover empty/nonempty removal, and generated `native_children_remove` contains `HashTablePrimitives.is_empty` while the public native-model tests pass. Dense-rank reuse beyond this deletion helper, operation measurements, and HP2's gate remain open. |
| 2026-09-22 | HP2.2 (dense-rank reuse) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. New private `*_at` branch helpers take a previously computed dense index. Public `native_set` and `native_remove` compute `native_rank bitmap slot` once per branch dispatch, use that index for lookup and for replace/insert/remove, and preserve existing source refinement through new direct helper lemmas. Generated inspection confirms one bound index feeds each hot branch helper. Persistence/operation matrix measurements and HP2's gate remain open. |
| 2026-09-22 | HP2.2 smoke measurement | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Public generated existing/new set and present/missing remove allocated 197,320 / 221,040 / 172,776 / 179,592 bytes. This is a local single-sample smoke observation after rank reuse, not the required HP2 stage matrix or a portable performance claim. |
| 2026-09-22 | HP0.3 matrix runner | `HASHTABLE_MATRIX_SIZES=100 HASHTABLE_MATRIX_SEEDS=31 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_MATRIX_OUTPUT=/tmp/hashtable-matrix-smoke2 sh ./run-hashtable-performance-matrix.sh` | Passed: six distribution-specific JSONL files were written for integer ascending/shuffled/root-slot-collision and string fixed-width/mixed-length/common-prefix workloads. The runner defaults to the planned four sizes, three seeds and seven repetitions when explicitly invoked outside CI. It exposed and fixed a root-slot-collision harness bug: the previous new-key set overlapped existing multiple-of-32 keys. Full matched matrix, Patricia inputs and attribution remain open. |
| 2026-09-22 | HP1.2 target-domain guard | `make hashtable-scalar-test hashtable-native-array-extracted-test-native` | Passed. Scalar bitmap operations now reject negative or wider-than-32-bit values, joining the existing slot/hash/depth and 64-bit platform guard. The primitive corpus checks rejection of negative bitmap, 33rd-bit bitmap and 30-bit-overflow hash inputs; the extracted native model suite still passes. Public range-closure proof and the HP1 gate remain open. |
| 2026-09-22 | HP3.1 direct empty/leaf set/remove slice | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTable.v`; `make hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. `native_set` directly creates an empty leaf, replaces a matching leaf and creates a same-hash two-entry collision; `native_remove` directly preserves/removes empty and leaf cases. Their refinement lemmas reuse new source leaf equations. Generated inspection confirms empty and leaf cases contain no source conversion; distinct-hash leaf joins and collision updates/removals still fall back. The single-sample 100-binding smoke measured public build / existing set / new set / present remove / missing remove allocation at 344,904 / 190,920 / 221,040 / 156,776 / 179,592 bytes. This is not the required HP3 matrix or gate closure. |
| 2026-09-22 | HP3.2 indexed-worker length prerequisite | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableArrayRefinement.v`; `make hashtable-native-primitives-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `pseq_length` has a view theorem and is mapped only at the native array extraction boundary to `HashTablePrimitives.length` (`Array.length`). The sequence refinement contract and primitive corpus now cover this operation. Collision workers have not yet been routed through it, so HP3.2 remains open. |
