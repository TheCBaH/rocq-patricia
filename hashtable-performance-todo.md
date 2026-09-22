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
  Partial: both HAMT harnesses now prepare per-sample inputs before timing,
  retain an observable checksum, validate results afterward, and distinguish
  first-wins loading from repeated replacement. The string harness also covers
  hit/miss lookup and membership, existing/new set, present/missing remove and
  enumeration for its four implementations. A matched Patricia comparison is
  still absent.
- [ ] **HP0.2** Add latest-root/all-prefix timed policies and controlled live-heap
  measurement with all roots alive; separate mutable single-version results.
- [ ] **HP0.3** Add matched Patricia/AVL/Hashtbl/HAMT integer/string distributions,
  sizes, seeds, repetitions and machine-readable environment/revision metadata.
  Partial: the integer runner now includes the constant-hash workload at the
  planned 100/2,000 cap and labels larger-size omissions. The public and
  standalone HAMTs use the supplied constant callback; `Map` and `Hashtbl`
  retain their own comparison/hashing policies.
- [x] **HP0.4** Profile scalar operations, conversions, primitive copies and
  hashing, or record controlled microbenchmark attribution and its limitations.
  No compatible profiler is installed locally. `hashtable-primitive-benchmark`
  is the recorded fallback; it isolates checked scalar calls, the hash callback,
  sequence get, fresh edits and `to_list`. It does not attribute call counts
  inside whole-map operations, so it is not a substitute for a sampling trace.
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

- [x] **HP2.1** Add proved sequence emptiness and its array contract/binding;
  replace deletion's child-view check and reprove refinement.
- [x] **HP2.2** Reuse computed dense ranks through private helpers, preserving
  insertion versus existing-child bounds.
- [x] **HP2.3** Record bounded/option-free indexing decision from profile; keep
  checked indexing unless new call-site proof and measurable benefit justify it.
  Decision: retain checked `pseq_get` and fresh edits. The residual smoke
  profile is insufficiently attributed to justify an option-free primitive,
  and collision sequences are not bounded by branch width.
- [ ] **HP2.G** Generated deletion has no child-list emptiness conversion;
  persistence and operation tests pass; stage measurements recorded.

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
