# Generated HAMT performance tracker

Last updated: 2026-09-23.
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

- [x] **HP0.1** Move oracle work/input-value creation outside timing; consume and
  validate measured results; separate repeated-set build and first-wins `of_list`.
  Both integer/string harnesses prepare per-sample inputs before timing, retain
  observable checksums, validate maps/enumeration afterward, and distinguish
  first-wins loading from repeated replacement across their four implementations.
- [x] **HP0.2** Add latest-root/all-prefix timed policies and controlled live-heap
  measurement with all roots alive; separate mutable single-version results.
  Persistent existing/new-set tasks explicitly time both policies; the all-prefix
  task retains each root in its sample slot through allocation measurement and
  validates newest/oldest versions. Post-GC live heap is reported separately;
  `Hashtbl` remains a prepared single-version comparison.
- [x] **HP0.3** Add matched Patricia/AVL/Hashtbl/HAMT integer/string distributions,
  sizes, seeds, repetitions and machine-readable environment/revision metadata.
  The integer runner includes the constant-hash workload at the
  planned 100/2,000 cap and labels larger-size omissions. The public and
  standalone HAMTs use the supplied constant callback; `Map` and `Hashtbl`
  retain their own comparison/hashing policies. JSONL sample and summary
  records now carry explicit `history_policy` values. `PatriciaMatrixBenchmark`
  now supplies a process-level matched integer companion with the same input,
  operation, retention, validation, warmup/repetition, and JSONL-metadata
  boundary. `PatriciaStringMatrixBenchmark` now supplies the same companion
  for the fixed-width, mixed-length, and common-prefix string distributions.
  The integer matrix also supplies seed-normalized `divergence-depth-0` through
  `divergence-depth-5` keys, with the same positive inputs for HAMT and
  Patricia; these expensive later-depth collision shapes are capped at
  100/2,000 bindings. Its files are deliberately separate because directly
  linking the two extraction trees collides on shared un-namespaced support
  modules. A 100-binding runner smoke wrote and metadata-validated all 26
  paired records (ten integer and three string distributions); the full
  repeated size/seed matrix remains HP5.3 evidence.
- [x] **HP0.4** Profile scalar operations, conversions, primitive copies and
  hashing, or record controlled microbenchmark attribution and its limitations.
  No compatible profiler is installed locally. `hashtable-primitive-benchmark`
  is the recorded fallback; it isolates checked scalar calls, the hash callback,
  sequence get, fresh edits and `to_list`. It does not attribute call counts
  inside whole-map operations, so it is not a substitute for a sampling trace.
- [ ] **HP0.G** Publish corrected baseline and remaining attribution uncertainty.

- [x] **HP1.1** Define bounded scalar wrappers and source popcount; prove
  equivalence to `HashTableBits` and range closure for reachable calls.
  Transparent wrappers expose kernel-checked local bounds for chunk, bitmap
  bit, rank, insertion at an absent slot, and deletion. Public lookup,
  set/remove, direct join, and first-wins loading safety theorems compose
  normalized hash, the six-level depth bound, recursively reached branch
  bitmap bounds, and stored-hash bounds from `native_table_wf`.
- [x] **HP1.2** Add small OCaml scalar realizers/extraction bindings, platform
  guard and complete primitive/foreign-obligation inventory.
  `HashTableScalarPrimitives` supplies guarded 64-bit bounded operations;
  extraction and primitive-inventory audits name every approved binding and
  document target execution as a foreign contract.
- [x] **HP1.3** Register new modules in proof, assumption audit, extraction,
  bytecode/native link recipes and clean rules.
  The scalar source is in `HASHTABLE_VFILES`/assumption checks, both runtime
  link lists, every native extraction consumer, the aggregate, and clean rules.
- [x] **HP1.4** Add model-vs-target scalar tests across slot/hash/bitmap/depth
  boundaries, full 16-bit popcount corpus and random 32-bit patterns.
  The same corpus now runs through explicit bytecode and native targets: all
  slots, hashes 0/`2^30-1`, depths 0–6, all 16-bit words, 10,000 deterministic
  32-bit masks, full bitmap, and invalid target-domain inputs.
- [ ] **HP1.G** Proof/audit/test pass; generated arithmetic inspection and isolated
  scalar-stage measurements recorded against HP0.

- [x] **HP2.1** Add proved sequence emptiness and its array contract/binding;
  replace deletion's child-view check and reprove refinement.
- [x] **HP2.2** Reuse computed dense ranks through private helpers, preserving
  insertion versus existing-child bounds.
- [x] **HP2.3** Record bounded/option-free indexing decision from profile; keep
  checked indexing unless new call-site proof and measurable benefit justify it.
  Decision: retain checked `pseq_get` and fresh edits. The residual smoke
  profile is insufficiently attributed to justify an option-free primitive,
  and collision sequences are not bounded by branch width.
- [x] **HP2.G** Generated deletion has no child-list emptiness conversion;
  persistence and operation tests pass; stage measurements recorded.
  `native_children_remove` uses the refined emptiness primitive, and generated
  hot-worker audits reject a sequence view in public deletion. The aggregate
  bytecode/native persistence suites and the recorded rank-reuse smoke provide
  the required operation evidence; later HP3 workers do not revert the path.

- [x] **HP3.1** Implement/prove direct native empty/leaf/join workers; preserve
  total model fallback behavior or prove a separate valid-public-worker bridge.
  `native_set` and `native_remove` handle every native constructor directly;
  `native_join_worker` constructs compact paths for distinct hashes, and
  zero-fuel branches retain their native tree directly.
- [x] **HP3.2** Implement/prove indexed sequence collision workers, termination,
  representative retention and empty/singleton normalization; test buckets >32.
  The private sequence contract exposes a refined length operation, extracted
  as `Array.length`, for bounded indexed workers. Lookup/update/removal use
  one length-bounded checked traversal; update/removal normalize arbitrary
  empty/singleton collision sequences without a view conversion.
- [x] **HP3.3** Lift worker proofs to native public validity/lookup/set/remove/
  first-wins loading; preserve seed, callback and arbitrary-payload contracts.
  `native_table_*_refines`, `native_table_wf_*`, pointwise update/removal and
  `source_table_native_of_list` retain these source-level contracts.
- [x] **HP3.4** Separate proof/test conversions from public operation paths and
  record enumeration strategy and its measured allocation.
  Decision: retain source-tree conversion for `elements` only. It is outside
  the hot operation set, intentionally materializes an enumeration list, and
  its allocation remains reported separately by the benchmark.
- [x] **HP3.G** Generated public get/mem/set/remove/of_list paths avoid source
  round trips and sequence-to-list conversion; full semantic matrix passes.
  Generated hot-worker audits reject conversions; bytecode/native differential
  tests cover collision buckets >32, normalization, routing depths 0–5 and
  retained histories. Enumeration remains the documented exception.

- [x] **HP4.D** Record residual profile and explicit implement/defer decision.
  Defer layout specialization. The HP3 smoke still shows generated public
  allocation above the standalone backend (for example, 124,272/40,376 bytes
  for 100-binding build and 113,952/4,944 for hit lookup), but HP0.4 has not
  attributed that residual among callbacks, checked options and fresh copies.
  A fixed 32-cell layout or unsafe indexing is therefore not justified.
- [x] **HP4.G** If selected, each sequence/layout/changed-result experiment has
  model proof, target contract, audit, persistence tests and isolated results;
  otherwise record why the stage is deferred. No candidate was selected;
  preserving compact fresh arrays avoids an unmeasured retained-space tradeoff.

- [x] **HP5.1** Strengthen generated public-call-path and extraction-binding
  audits, add negative fixtures, replace obsolete required-fallback checks.
  The native-array audit rejects source-tree/sequence-view use in generated
  get/set/remove/first-wins loading and requires recursive public workers; its
  negative-fixture target proves rejection of an injected hot `to_list` and a
  non-recursive `native_set` override. The list-model audit now requires the
  direct join/collision workers rather than obsolete source fallbacks.
- [x] **HP5.2** Run `make hashtable-proof hashtable-assumptions`, `make hashtable`,
  `make all`, `make hashtable-benchmark-smoke`; integrate proposed new checks.
  The hash-table aggregate (including proof/assumption and generated audits),
  repository aggregate, and two-harness 100-entry benchmark smoke all pass.
- [ ] **HP5.3** Run clean-checkout aggregate and matched repeated performance
  matrix; record achieved/unmet targets and any repeatable regressions.
  Partial: the local 2,000-entry three-seed matrix completed with three
  repetitions plus a warmup for all current HAMT integer/string distributions.
  A fresh detached worktree now passes `make all`, and the matrix has matched
  integer Patricia records. A fresh detached worktree now also passes the
  expanded 100-binding paired matrix smoke (all 26 records, including strings
  and routing depths). It still lacks the planned repeated 100/2,000/10,000/
  100,000 points and a clean-worktree full matrix.
- [x] **HP5.4** Update README, performance note and release/foreign-contract
  inventories; retain source proof versus target testing distinction.
  `README.md`, `hashtable-performance.md`, and
  `hashtable-reference-release.md` now describe scalar/direct-worker status,
  enumeration's explicit exception, model-only source oracles, and the
  remaining foreign/runtime and measurement limits.
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
| 2026-09-22 | HP0.1 (fixed-width string, partial) | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=2 make hashtable-string-benchmark` | Passed. The string harness now uses the same warmup/repetition, allocation, JSONL-metadata and observable-result boundary as the integer harness. Timed lookup computes only a checksum; the independent lookup oracle runs after timing. Mutable update/removal trials copy their prepared table, so repeated samples do not mutate the next sample's input. The later HP0.1 entry expands its operation coverage; matched Patricia and attribution remain open. |
| 2026-09-22 | HP0.2/HP0.3 (string distributions, partial) | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_STRING_PATTERN=common-prefix make hashtable-string-benchmark` | Passed. The harness accepts `fixed-width`, `mixed-length`, and `common-prefix` (192-byte prefix) deterministic byte-string inputs, labels JSONL records with the chosen distribution, and now separately measures latest-root and all-prefix live heap for every persistent implementation. The smoke target pins fixed-width. The later HP0.1 entry adds miss/membership/enumeration operations; matched Patricia inputs, repeated full matrix and profiler attribution remain open. |
| 2026-09-22 | HP1.1–HP1.4 (lookup-routing scalar slice) | `make hashtable-proof hashtable-native-array-extraction-audit hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-scalar-test`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. `HashTableNativeBits.v` defines transparent scalar wrappers with closed equality lemmas; generated `native_get` now reaches checked 64-bit OCaml chunk, bitmap-membership and rank realizers. The adapter is tested across every slot, all 16-bit bitmap words, 10,000 deterministic 32-bit masks, bitmap extremes, hashes 0/`2^30-1`, and depths 0–6. The extraction audit requires these bindings and scalar routing in `native_get`; bytecode/native model tests passed. Before the following set-routing change, the 100-binding smoke measured public lookup-hit allocation at 113,952 bytes (previous corrected smoke: 3,260,640). Range closure at the public API, scalar routing for removal, complete aggregate links, stage measurement matrix and all HP1 closure conditions remain open. |
| 2026-09-22 | HP1.1–HP1.4 (set-routing scalar slice) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test-native hashtable-scalar-test`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. Generated `native_set` now uses the same source-defined chunk, bitmap-membership and rank wrappers; its existing source refinement proof closes after explicit conversion between the transparent wrapper and model forms. The extraction audit requires both public get and set workers to contain scalar routing. The smoke measured public `of_list` build / existing set / new set allocation at 2,208,888 / 2,404,136 / 2,734,800 bytes, down from the prior corrected 100-binding smoke's 5,761,848 / 8,697,512 / 8,600,112. Removal and source-join fallback scalar work remain open; no stage gate is closed. |
| 2026-09-22 | HP1.1–HP1.4 (remove-routing scalar slice) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. Generated `native_remove` now uses bounded scalar chunk, membership and rank routing while retaining the established source-model bitmap-edit helpers. Its existing refinement theorem closes with transparent wrapper conversions. The audit now requires all three public get/set/remove workers to route through the scalar chunk binding. The 100-binding smoke measured public present/missing removal allocation at 2,650,952 / 1,550,736 bytes, down from 5,797,320 / 7,191,632 before scalar routing. Join/source-fallback arithmetic, range-closure theorems, full matrix and HP1 gate remain open. |
| 2026-09-22 | HP1.1–HP1.4 (branch bitmap/edit scalar slice) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit hashtable-scalar-test` | Passed. Native branch replace/insert/remove now call scalar dense-rank and bitmap insert/delete wrappers, with the existing refinement proofs closing by transparency. Generated source contains scalar rank at branch edits and scalar insert/delete bindings; the audit requires all five approved scalar operations. Source-join fallback arithmetic, range closure, full aggregate and stage matrix remain open. |
| 2026-09-22 | HP2.1 (sequence emptiness) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableArrayRefinement.v`; `make hashtable-native-primitives-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `pseq_is_empty` has a source view theorem; `array_sequence_contract` now requires and refines an emptiness operation. `native_children_remove` calls it instead of materializing the child view. The array adapter realizes it with `Array.length = 0`; primitive tests cover empty/nonempty removal, and generated `native_children_remove` contains `HashTablePrimitives.is_empty` while the public native-model tests pass. Dense-rank reuse beyond this deletion helper, operation measurements, and HP2's gate remain open. |
| 2026-09-22 | HP2.2 (dense-rank reuse) | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. New private `*_at` branch helpers take a previously computed dense index. Public `native_set` and `native_remove` compute `native_rank bitmap slot` once per branch dispatch, use that index for lookup and for replace/insert/remove, and preserve existing source refinement through new direct helper lemmas. Generated inspection confirms one bound index feeds each hot branch helper. Persistence/operation matrix measurements and HP2's gate remain open. |
| 2026-09-22 | HP2.2 smoke measurement | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Public generated existing/new set and present/missing remove allocated 197,320 / 221,040 / 172,776 / 179,592 bytes. This is a local single-sample smoke observation after rank reuse, not the required HP2 stage matrix or a portable performance claim. |
| 2026-09-22 | HP0.3 matrix runner | `HASHTABLE_MATRIX_SIZES=100 HASHTABLE_MATRIX_SEEDS=31 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_MATRIX_OUTPUT=/tmp/hashtable-matrix-smoke2 sh ./run-hashtable-performance-matrix.sh` | Passed: six distribution-specific JSONL files were written for integer ascending/shuffled/root-slot-collision and string fixed-width/mixed-length/common-prefix workloads. The runner defaults to the planned four sizes, three seeds and seven repetitions when explicitly invoked outside CI. It exposed and fixed a root-slot-collision harness bug: the previous new-key set overlapped existing multiple-of-32 keys. Full matched matrix, Patricia inputs and attribution remain open. |
| 2026-09-22 | HP0.3 constant-hash benchmark | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_PATTERN=constant-hash HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. The integer harness uses the supplied deterministic constant callback only for the two HAMT implementations; `Map` and `Hashtbl` retain their normal policies. The matrix runner includes this workload at sizes 100/2,000 and explicitly skips 10,000/100,000 because the planned collision history is quadratic. This single sample measured public generated build / hit lookup / existing set / new set / present remove allocation at 1,200,744 / 412,144 / 1,245,784 / 3,524,584 / 74,744 bytes. It is collision-path evidence, not a repeated matrix result. |
| 2026-09-22 | HP0.3 constant-hash 2,000 matrix point | `HASHTABLE_BENCH_SIZE=2000 HASHTABLE_BENCH_PATTERN=constant-hash HASHTABLE_BENCH_REPETITIONS=3 HASHTABLE_BENCH_WARMUPS=1 make hashtable-benchmark` | Passed. The capped expensive workload now has its planned 2,000-entry repeated point. Public generated median build / hit lookup / existing set / new set / present remove allocation was 464,823,544 / 160,240,144 / 480,912,184 / 1,392,888,184 / 16,695,944 bytes; time was 30.776 / 8.221 / 34.896 / 87.872 / 10.695 ms. The result confirms collision-heavy costs remain separate from ordinary distributions and does not compare hashing policy with `Map`/`Hashtbl`. |
| 2026-09-22 | HP1.2 target-domain guard | `make hashtable-scalar-test hashtable-native-array-extracted-test-native` | Passed. Scalar bitmap operations now reject negative or wider-than-32-bit values, joining the existing slot/hash/depth and 64-bit platform guard. The primitive corpus checks rejection of negative bitmap, 33rd-bit bitmap and 30-bit-overflow hash inputs; the extracted native model suite still passes. Public range-closure proof and the HP1 gate remain open. |
| 2026-09-22 | HP3.1 direct empty/leaf set/remove slice | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTable.v`; `make hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. `native_set` directly creates an empty leaf, replaces a matching leaf and creates a same-hash two-entry collision; `native_remove` directly preserves/removes empty and leaf cases. Their refinement lemmas reuse new source leaf equations. Generated inspection confirms empty and leaf cases contain no source conversion; distinct-hash leaf joins and collision updates/removals still fall back. The single-sample 100-binding smoke measured public build / existing set / new set / present remove / missing remove allocation at 344,904 / 190,920 / 221,040 / 156,776 / 179,592 bytes. This is not the required HP3 matrix or gate closure. |
| 2026-09-22 | HP3.2 indexed-worker length prerequisite | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableArrayRefinement.v`; `make hashtable-native-primitives-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `pseq_length` has a view theorem and is mapped only at the native array extraction boundary to `HashTablePrimitives.length` (`Array.length`). The sequence refinement contract and primitive corpus now cover this operation. Collision workers have not yet been routed through it, so HP3.2 remains open. |
| 2026-09-22 | HP3.2 indexed collision lookup slice | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableBucket.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `make hashtable-proof hashtable-assumptions hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `native_bucket_get` walks checked `pseq_get` indexes bounded by `pseq_length`; its source-index theorem proves equivalence to `bucket_get`. Generated collision lookup calls it with `HashTablePrimitives.length`, and the audit requires that route. Bytecode/native model tests explicitly check every hit and a miss in a 40-entry collision bucket. Collision update/removal, singleton/empty normalization and a collision-specific measurement remain open. |
| 2026-09-22 | HP3.2 indexed collision update slice | `make hashtable-proof hashtable-assumptions hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `native_bucket_set` walks a checked index bounded by one `pseq_length`, using fresh `pseq_replace` on a hit (retaining the resident key) and `pseq_insert` on a miss. Its list-view theorem refines `bucket_set_index`; `native_normalize_collision` uses only length/get to preserve total empty/singleton behavior. Public `native_set` dispatches same-hash collisions directly through this worker; the distinct-hash join fallback remains. The generated audit requires the indexed update worker, and bytecode/native tests cover an existing-key update, append, and retained old version in a 40-entry collision bucket. Collision removal and a collision-specific measurement remain open. |
| 2026-09-22 | HP3.2 indexed collision removal slice | `make hashtable-assumptions hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `native_bucket_remove` walks the same checked, bounded index and uses a fresh `pseq_remove` only on a hit; its view theorem refines `bucket_remove_index`. Same-hash public `native_remove` now avoids source conversion and normalizes to leaf/empty through `native_normalize_collision`; a hash mismatch retains the collision directly. The generated audit requires the removal worker. Bytecode/native tests cover removal and retained history in a 41-entry collision plus two-entry normalization to leaf and then empty. Collision-specific measurement and the remaining HP3 join/public-reachability work are open. |
| 2026-09-22 | HP3.1 direct native join slice | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `make hashtable-proof hashtable-assumptions hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 make hashtable-benchmark` | Passed. `native_join_two` and the fuel-bounded `native_join_worker` construct compact native branches directly and refine `join_two`/`join_worker`. Distinct-hash leaf and collision updates use this worker instead of `source_of_native`/`native_of_source`; zero-fuel branches retain their native tree directly. The extraction audit requires the direct join worker and rejects source conversions in generated get/set/remove/first-wins loading. Bytecode/native tests compare source/native joins whose first divergence is each routing depth 0–5. The single-sample 100-binding smoke measured public build / existing set / new set / present remove / missing remove allocation at 124,272 / 182,920 / 213,040 / 150,376 / 173,192 bytes. This is not the required repeated or collision-specific matrix. |
| 2026-09-22 | HP5.1 native-array audit fixtures | `make hashtable-native-array-extraction-audit hashtable-native-array-extraction-audit-test` | Passed. The hot-worker shape audit now rejects source-tree and sequence-view conversion in public generated get/set/remove/first-wins loading and requires recursive get/set/remove definitions. Its fixture target injects `HashTablePrimitives.to_list` into `native_get` and changes recursive `native_set` into a whole-operation override; both must fail the audit. The target is included in `make hashtable`. Native-model audit replacement remains open. |
| 2026-09-22 | HP5.1 native-model audit update | `make hashtable-native-model-extraction-audit` | Passed. The list-model audit now requires length/emptiness operations, direct join and collision workers, indexed branch helpers, and no source-tree/sequence-view conversion in generated get/set/remove/first-wins loading. It no longer requires the HP3 source fallbacks. |
| 2026-09-22 | HP3.3/HP3.4/HP3.G and HP4 decision audit | `make hashtable-proof hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit hashtable-native-array-extraction-audit-test hashtable-native-model-extraction-audit` | Passed. Existing native-table refinement/well-formedness/pointwise/first-wins theorems were rechecked against the direct workers. Generated audits establish no source/view conversion in get/set/remove/first-wins loading; bytecode/native differential tests cover 40/41-entry collisions, normalization, depths 0–5 and retained roots. `elements` deliberately remains the sole source-conversion enumeration path. HP4 is deferred because smoke allocation identifies residual cost but does not yet attribute it sufficiently to justify a storage or unsafe-index experiment. |
| 2026-09-22 | HP0.4 isolated attribution | `HASHTABLE_PRIMITIVE_BENCH_ITERATIONS=100000 HASHTABLE_BENCH_REPETITIONS=3 HASHTABLE_BENCH_WARMUPS=1 make hashtable-primitive-benchmark` | Passed. No compatible profiler was found on the local toolchain, so this is the prescribed isolated fallback. Scalar chunk/bitmap-has/hash-callback loops each allocated 96 bytes per 100,000 calls; rank allocated 96 bytes and took 2.227 ms. A 32-entry private sequence allocated 1,600,096 bytes for checked gets, 25,600,096/27,200,096/26,400,096 bytes for remove/insert/replace fresh copies, and 80,800,096 bytes for `to_list`. The measurement isolates primitives rather than attributing their call counts in a whole-map operation. |
| 2026-09-22 | HP0.1 string operation coverage (partial) | `make hashtable-string-benchmark-smoke`; then `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_BENCH_STRING_PATTERN=common-prefix make hashtable-string-benchmark` and the same command with `mixed-length` | Passed. The string harness now matches the corrected operation boundary: first-wins `of_list` and repeated `set` builds; hit/miss lookup and membership; existing/new set; present/missing remove; and `elements`. It makes deterministic fresh/missing keys and all expected bindings before timing; persistent and mutable per-sample mutation inputs are distinct; post-timing checks validate maps and enumeration contents. Persistent maps report both retention policies and `Hashtbl` reports single-version heap. This 100-entry smoke across fixed-width, common-prefix and mixed-length inputs is not a matched Patricia comparison or a repeated full matrix. |
| 2026-09-22 | HP5.2 hash-table aggregate | `make hashtable` (detached status capture) | Passed, exit status 0. The first aggregate exposed that `HashTableNativeModelTest.ml` calls `HashTable.set_tree`/`remove_tree` but `HashTableExtract.v` did not separately extract them after direct workers removed their incidental reachability. Adding those source functions to the model-only extraction restored bytecode/native model differential tests; the re-run passed proof/assumption audits, extraction audits and all hash-table tests. `make all`, the release matrix and hosted CI remain open. |
| 2026-09-22 | HP5.2 repository aggregate and benchmark smoke | `make all` (detached status capture); `make hashtable-benchmark-smoke` | Both passed, each exit status 0. The repository aggregate completed its global assumption audit and Patricia oracle/differential suite. The benchmark smoke ran the corrected 100-binding integer and fixed-width string harnesses with all configured operations, generated JSONL records, and passed their semantic checks. This closes the local aggregate command requirement only; clean-checkout repetition, release documentation and hosted CI remain separate gates. |
| 2026-09-22 | HP5.4 release/performance documentation | Reviewed `README.md`, `hashtable-performance.md`, and `hashtable-reference-release.md`; `git diff --check` | Updated the public benchmark description, implementation/performance status, generated-audit scope, source-model extraction purpose, and direct collision-worker evidence. The documents distinguish kernel source/refinement theorems from foreign OCaml contracts and finite bytecode/native tests; they retain profiling, matched-matrix, and CI limits. |
| 2026-09-22 | HP0.3/HP5.3 repeated 2,000-entry matrix (partial) | `HASHTABLE_MATRIX_SIZES=2000 HASHTABLE_MATRIX_SEEDS='0 31 104729' HASHTABLE_BENCH_REPETITIONS=3 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_MATRIX_OUTPUT=/tmp/patricia-hamt-matrix.CIroDu/records sh ./run-hashtable-performance-matrix.sh`; JSONL metadata/summary validation with `jq` | Passed, exit status 0. All 21 expected records exist: ascending, shuffled, root-slot-collision, capped constant-hash, fixed-width, mixed-length, and common-prefix workloads for each seed. Every record declares size 2,000, three repetitions, and one warmup. It is reproducible repeated local evidence, but not the required four-size matrix, clean-checkout result, or a matched Patricia comparison. |
| 2026-09-22 | HP1.1 scalar local range contracts | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeBits.v`; `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNative.v`; `make hashtable-scalar-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` | Passed. `HashTableNativeBits.v` now proves wrapper-local bounds for chunk, bitmap bit, rank, insertion, and deletion by the existing source scalar lemmas. Insertion explicitly requires an absent slot, matching branch insertion rather than claiming an unconstrained bitwise-or contract. This is local model evidence only: deriving valid bitmap and call-site hypotheses from a public native table remains HP1.1's open range-closure portion. |
| 2026-09-22 | HP0.1/HP0.2 corrected operation and history policies | `make hashtable-benchmark-smoke`; `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_BENCH_STRING_PATTERN=common-prefix make hashtable-string-benchmark`; `git diff --check` | Passed. Both persistent harnesses now separately time existing/new set with latest-root and all-prefix-root policies, retaining all roots through the timed allocation boundary and checking every policy's latest/oldest result afterward. The integer `Hashtbl` branch now also prepares independent mutable update/add/remove inputs outside timing and validates all operation/enumeration outputs, matching the string boundary. The fixed-width smoke and common-prefix run cover all configured operations; cross-family matched distributions remain HP0.3 work. |
| 2026-09-22 | HP0.3 history-policy JSONL metadata | `HASHTABLE_BENCH_SIZE=10 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_BENCH_RESULTS=<mktemp> make hashtable-benchmark`; `jq` assertions on samples/summaries | Passed. Each timing sample and summary now carries `history_policy`; the smoke validates `latest-root` for ordinary persistent updates, `all-prefix-roots` for retained histories, and `single-version` for `Hashtbl`. The field complements operation labels and live-heap records so external matrix processing need not infer a policy from names. |
| 2026-09-22 | HP1.4 bytecode/native scalar corpus | `make hashtable-scalar-test-bytecode hashtable-scalar-test`; `git diff --check` | Passed. The full target-domain corpus now runs in both bytecode and native code; the bytecode target is included in `make hashtable` and clean rules. It validates scalar behavior, not the separate public-call range-closure theorem. |
| 2026-09-22 | HP1.2/HP1.3 scalar inventory and aggregate integration | `make hashtable-scalar-primitives-audit hashtable-scalar-test-bytecode hashtable-scalar-test`; then `make hashtable` (detached status capture) | Passed, aggregate exit status 0. The scalar audit confirms each approved guarded binding, domain checks, 32-step popcount, and no unsafe escape; the extraction audit confirms bindings reach generated workers. `make hashtable` runs the source proof/assumption audit, both scalar execution modes, bytecode/native model suites, and all declared runtime link paths. Public scalar range closure and the stage matrix remain HP1.G work. |
| 2026-09-22 | HP1.1 public lookup scalar closure | `make hashtable-proof hashtable-assumptions hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit` (detached status capture) | Passed, exit status 0. `native_get_scalar_safe_wf` follows the exact `pseq_get` child selected by a generated lookup from source `wf`, preserving the normalized hash and six-level depth bound and extracting each branch bitmap bound. `native_table_get_scalar_safe` lifts that invariant from `native_table_wf` at the public root. Set/remove branch and direct-join scalar reachability are deliberately not claimed by this lookup theorem. |
| 2026-09-22 | HP1.1 public update/join scalar closure | `/opt/opam/4.14.3/bin/rocq compile -q -Q . '' HashTableNativeProof.v`; `make hashtable-native-array-extracted-test hashtable-native-array-extracted-test-native hashtable-native-array-extraction-audit hashtable-scalar-primitives-audit hashtable-scalar-test-bytecode hashtable-scalar-test` | Passed. `native_update_scalar_safe_wf` follows update/removal branch routing through the source well-formed child relation and proves stored leaf/collision hashes for direct joins. Its public set/remove corollaries, plus the bounded recursive join invariant, cover every scalar call in those operations. The theorem is intentionally per operation; it does not yet induct over `native_table_add_first`/`of_list`. |
| 2026-09-22 | HP1.1 public first-wins-loader scalar closure | `make hashtable` (detached status capture) | Passed, exit status 0. `native_table_add_first_scalar_safe_wf` inducts over first-wins loading: every entry first satisfies lookup's scalar domain, and an absent entry also satisfies set's domain before continuing from the refined updated table. `native_table_of_list_scalar_safe` initializes that invariant from `native_empty`; together with the existing public lookup/set/remove and join theorems this closes source-level reachable scalar calls under normalized public hashes and `native_table_wf`. The foreign OCaml bindings remain explicit audited contracts, not kernel-checked target code. |
| 2026-09-22 | HP0.3 matched integer Patricia process boundary | `make hashtable-benchmark-smoke`; `HASHTABLE_MATRIX_SIZES=100 HASHTABLE_MATRIX_SEEDS=31 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_MATRIX_OUTPUT=<tmp> sh ./run-hashtable-performance-matrix.sh`; `jq` metadata/coverage assertions | Passed, exit status 0. `PatriciaMatrixBenchmark.ml` runs the same positive integer inputs, first-wins/repeated-set/lookup/membership/update/removal/enumeration operations, root-retention checks, timing protocol, and JSONL schema as the HAMT integer benchmark for public Patricia, `Stdlib.Map`, and `Hashtbl`. The matrix smoke emitted paired HAMT/Patricia files for ascending, shuffled, root-slot-collision, and constant-hash workloads; metadata agrees on workload/size/seed/repetitions/warmups and Patricia supplies 13 summaries plus both persistent live-heap policies. Separate executables are required because the generated support-module names collide. Matched strings and the full repeated clean matrix remain open. |
| 2026-09-22 | HP5.3 clean aggregate | Fresh detached worktree at `115c40a`, then `make all` (detached status capture) | Passed, exit status 0. The first clean run exposed an ordering defect: the global assumption script audits all `.v` files, but `make all` had not built HAMT `.vo` files first. `all` now depends on `hashtable-proof` before `assumptions`; the clean re-run compiled both proof families, reported 1,161 declarations closed under the global context, and passed extraction, audits, randomized oracle, union oracle, and optimized/reference differential tests. The clean performance matrix remains separate work. |
| 2026-09-22 | HP5.3 clean matrix smoke | Fresh detached worktree at `7b0c3c7`, then `HASHTABLE_MATRIX_SIZES=100 HASHTABLE_MATRIX_SEEDS=31 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_MATRIX_OUTPUT=<tmp> sh ./run-hashtable-performance-matrix.sh` (detached status capture) | Passed, exit status 0. The first clean matrix attempt exposed a second cached-artifact defect: `hashtable-benchmark` depended on `HashTableScalarPrimitives.cmx` without a build rule. The explicit native-object rule now rebuilds it. The clean re-run emitted 11 files: paired HAMT/Patricia integer records for four workloads and three current string records. This is a clean smoke only; the planned repeated four-size matrix and matched Patricia strings remain open. |
| 2026-09-22 | HP0 named baseline target | `make hashtable-performance-baseline` (detached status capture) | Passed, exit status 0. The new named target runs the 100-entry corrected HAMT integer/string smoke and matched Patricia integer companion with the ordinary seven measured repetitions. It is a reproducible local baseline smoke, not the full performance matrix. |
| 2026-09-23 | HP0.3 matched string Patricia process boundary | `HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_SEED=31 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_BENCH_STRING_PATTERN=fixed-width HASHTABLE_BENCH_RESULTS=<tmp> make patricia-string-matrix-benchmark`; `jq` metadata/sample assertions; `make hashtable-benchmark-smoke`; then the 100/seed-31/one-repetition matrix runner plus JSONL coverage and paired-metadata assertions | Passed. `PatriciaStringMatrixBenchmark.ml` uses exactly the fixed-width/mixed-length/common-prefix construction, operation boundaries, retained-root policies, validation, timing protocol, and JSONL schema of the HAMT string benchmark for direct string Patricia, `Stdlib.Map`, and `Hashtbl`. The focused smoke wrote 80 JSONL records and includes String Patricia samples; the aggregate 100-binding smoke then passed all four integer/string HAMT/Patricia executables at the ordinary seven measured repetitions. The updated runner wrote all 14 expected records, including a matching Patricia string JSONL file for each HAMT string distribution with identical workload/size/seed/repetition/warmup metadata. Process separation avoids generated support-module collisions. |
| 2026-09-23 | HP0.3 divergence-depth distributions | 100/seed-31/one-repetition matrix runner after adding `divergence-depth-0` through `divergence-depth-5`; JSONL metadata and paired-record assertions | Passed. The expanded runner wrote 26 records: paired HAMT/Patricia results for four ordinary integer distributions, six explicit routing-divergence depths, and three string distributions. The generators use the seed to ensure their HAMT hashes share every chunk before the named depth while retaining strictly positive, disjoint base/fresh/missing keys for the Patricia domain. Depth workloads are capped at 100/2,000 because their shrinking remaining hash domain creates collision histories at larger sizes. |
| 2026-09-23 | HP0.3 capped depth-5 point | `HASHTABLE_BENCH_SIZE=2000 HASHTABLE_BENCH_SEED=31 HASHTABLE_BENCH_PATTERN=divergence-depth-5 HASHTABLE_BENCH_REPETITIONS=1 HASHTABLE_BENCH_WARMUPS=1 make hashtable-benchmark`; same environment with `make patricia-matrix-benchmark`; JSONL assertions | Passed. Both paired executables completed the most collision-prone capped routing-depth workload at 2,000 bindings and wrote matching metadata plus timing samples. This validates the upper capped point; it is one repetition rather than the final repeated matrix. |
| 2026-09-23 | HP5.3 clean expanded matrix smoke | Fresh detached worktree at `866edb1`, then the 100/seed-31/one-repetition matrix runner with JSONL coverage and pairing assertions | Passed. A clean checkout rebuilt both extraction families and emitted all 26 expected records: paired HAMT/Patricia outputs for ordinary, constant-hash, and depth-0–5 integer inputs, plus the three paired string inputs. Every file has the requested metadata and sample records; every string/depth HAMT file has an equal-metadata Patricia peer. This is reproducible clean smoke evidence, not the repeated four-size matrix. |
