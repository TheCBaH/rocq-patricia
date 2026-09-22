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
- [ ] **HP3.2** Implement/prove indexed sequence collision workers, termination,
  representative retention and empty/singleton normalization; test buckets >32.
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
