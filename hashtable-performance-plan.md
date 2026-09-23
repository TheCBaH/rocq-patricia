# Generated HAMT performance: feasibility and implementation plan

Date: 2026-09-22. Status: HP0–HP4 implementation complete; HP5 repeated
matrix/reproducibility evidence in progress.
Evidence and historical measurements: [performance note](hashtable-performance.md).
Progress: [performance tracker](hashtable-performance-todo.md).
The [design](hashtable-design.md) remains the API/representation contract;
the completed H0–H5 work has its own [tracker](hashtable-todo.md).

## Decision and implications

Proceed with a staged optimization of the generated public backend. The first
candidate is bounded native arithmetic, followed by source-defined workers
that avoid conversions. Keep fresh-copy compact arrays initially. The
standalone backend already uses these same array primitives with roughly
155 times less integer-build allocation on the recorded workload; changing
storage first would confound the more immediate extraction issues.

This is feasible without replacing the public map algorithm with handwritten
OCaml. The repository already demonstrates the required architecture in
`PatriciaExtract.v`, `NativeStringWorker.v` and
[the Patricia verification inventory](patricia-native-verification.md).
What is not established is how much each change will improve throughput or
whether HAMT will beat Patricia/AVL on a particular distribution.

Pure Rocq can express the logical results of shifts, array indexing and updates.
The missing correspondence is efficient machine execution, allocation and
identity, not the ability to specify their mathematical functionality.
Model those results and prove the algorithms in Rocq; realize small operations
with OCaml bitwise operators and private array operations at extraction.
This adds explicit primitive obligations to the trusted boundary. It does not
turn a foreign implementation into a kernel-checked OCaml program.

No API changes, CHAMP conversion, mutable/transient public map, new hash width,
union API, C stubs, `Obj` tricks or 32-bit port are part of this plan. Keep
generic key equivalence, seed stability, resident representatives, first-wins
`of_list`, arbitrary payloads and retained-version behavior. Constant-hash
collision buckets can grow beyond 32 and remain linear-time; native arithmetic
cannot remove that worst case.

## Evidence and priority

| Finding | Local evidence | Consequence |
| --- | --- | --- |
| Number representation is native, routing operations are not all native | `HashTableNativeArrayExtract.v`; regenerated `HashTableBits.ml`, `BinNat.ml`, `BinPos.ml` | Prioritize scalar realization; inspect the reachable operations, not just extracted types. |
| List materialization occurs during ordinary operations | `HashTableNative.v`: `native_children_remove`, collision case of `native_get`, fallback cases of `native_set`/`native_remove` | Introduce source-defined emptiness, leaf/join and collision workers. |
| Fresh array edits are shared by both HAMTs | `HashTablePrimitives.ml`, `HashMapNative.ml` | Retain storage initially; profile copy volume before changing its contract. |
| Collision and child storage currently share `pseq` | `native_tree` in `HashTableNative.v` | Any 32-entry specialization needs a branch-only contract; it cannot constrain all sequences. |
| The audit claiming enumeration-only conversion checks the standalone implementation | `check-hashtable-native-array-backend.sh`; weaker presence checks in `check-hashtable-native-array-extraction.sh` | Add generated public-call-path checks and negative fixtures. |
| Integer lookup timing includes a linear oracle search per key | `HashTableBenchmark.ml`: `check`/`oracle_get` | Existing integer lookup totals cannot estimate map-operation latency. |
| Retained histories are separate heap passes | `retained_versions` in both HAMT harnesses | Measure history retention explicitly; do not attribute timed allocation to retaining every prefix. |
| Build policies differ | HAMT `of_list` checks first occurrence, AVL folds additions, `Hashtbl` replaces | Separate repeated-`set` build from API `of_list` tests; use identical ordered inputs for comparisons. |

Both benchmark targets were regenerated and run successfully on 2026-09-22
using the Makefile's `/opt/opam/4.14.3/bin` tools (Rocq 9.2, OCaml 4.14.3).
Public/standalone build allocation was 215,905,264/1,394,040 bytes for integers
and 243,088,456/1,279,488 for strings. No profiler attribution or optimized
speedup is claimed. Existing generated files were inspected after regeneration.

## Primitive and proof boundary

Prefer a proposed `HashTableNativeBits.v` for bounded scalar wrappers and the
source-defined optimized popcount worker, with a small private
`HashTableScalarPrimitives.ml`/`.mli` target adapter. Names here and below are
proposals, not existing artifacts. Bind these through
`HashTableNativeArrayExtract.v`; leave the reference extraction unspecialized.
Do not map general `N`/`nat` operations globally without proving the domains
of every affected reachable caller. During staging, source join fallbacks
still call `HashTableBits`, so a wrapper used only by branch routing does not
optimize all operations; measure and document that intermediate state.

| Primitive/model | Target realization candidate | Required domain/result contract |
| --- | --- | --- |
| Hash chunk | `(h lsr (5 * depth)) land 31` | `0 <= h < 2^30`; public branch depths 0–5; explicitly handle depth 6 if fallback paths call it; result 0–31. |
| Bitmap bit/membership | `1 lsl slot`; `bitmap land bit <> 0` | `slot` 0–31; `bitmap` 0–`2^32-1`; full/slot-31 behavior included. |
| Bitmap insert/delete | `lor`; `land (lnot bit)` | Inputs and outputs remain unsigned 32-bit values represented by nonnegative OCaml ints; complement is only used under the mask. |
| Rank mask | `bitmap land ((1 lsl slot) - 1)` | slot 0 gives zero, slot 31 retains precisely bits 0–30; rank equals occupied slots below the slot. |
| Popcount scalar steps | native zero/even tests, right shift, bounded increment | Source-defined loop returns low-32-bit popcount, bounded by 32. First use a simple 32-step proved loop; consider clearing the lowest bit only after measurement. |
| Hash/slot equality and order | typed integer comparison | Only scalar comparison; preserve `Key.equal` for keys and never compare payloads. |
| Sequence emptiness/length | `Array.length` | `length target = length logical_view`; emptiness iff view is empty. |
| Sequence get/edit | existing checked get and fresh-copy edits | Existing total list-view laws and freshness; bounded fast variants require new call-site proofs. |

The existing design already selects 64-bit OCaml: 30-bit hashes and 32-bit
bitmaps fit its 63-bit integers. Add an executable platform guard and tests;
do not silently claim support for 31-bit integers. Bound all shift counts and
intermediates, including depth multiplication and any later popcount formula.
Do not replace saturating natural subtraction or arbitrary shifts with machine
operators outside their proved domains.

Prove source equivalence and reachable-call range closure separately. Existing
`native_*_refines` statements cover arbitrary modeled trees/fuel. Preserve
those total model theorems where possible, or introduce a separately named
optimized worker with explicit validity hypotheses and discharge them at the
public root. Never quietly weaken an existing theorem to justify an extraction
binding. Raw private test workers also need their domain documented.

`HashTableArrayRefinement.v` quantifies an `array_sequence_contract`; its
`array_fresh` predicate is abstract. Neither that predicate nor a passing audit
establishes target heap noninterference by itself. Retain private arrays, fresh
updates and unchanged input contents as the reviewed OCaml obligations. Empty
arrays may share a runtime representation; observational persistence is the
essential property, not an unconditional physical-inequality test. A stronger
target heap proof would be a separate verification project.

## Delivery stages

### HP0 — Establish measurements and extraction inventory

Dependencies: none. Estimated relative effort: small to medium.

1. Update `HashTableBenchmark.ml` and `HashTableStringBenchmark.ml`, factoring
   shared harness code if useful. Precompute keys, values and expected results
   outside timing. Keep an independently checked semantic pass; consume timed
   results through an observable checksum or retained result to prevent dead
   work elimination. Report harness/checksum allocation separately.
2. Separate build-by-`set`, `of_list`, hit/miss lookup, membership, existing/new
   key update, present/missing removal and enumeration. Prepare fresh input
   maps for each trial; reset mutable tables outside each measured update run.
3. Implement latest-root and all-prefix policies for timed persistent updates
   and separate post-GC live-heap measurements. Keep roots demonstrably live
   through measurement; account for the root list itself. Report mutable
   tables as single-version only.
4. Use identical positive integer keys for comparisons including Patricia;
   include the original zero-based HAMT case separately. Use identical string
   bytes for all string maps. Hash callbacks/seeds must match the two HAMTs;
   report `Hashtbl`'s own hashing policy rather than assuming equivalence.
5. Save machine-readable records with source revision, dirty state, OS/CPU,
   word size, compiler/configuration, GC parameters, size, seed, distribution,
   history policy and repetition. Warm up; run at least seven measured
   repetitions, rotate implementation order and report median/min/max.
6. Profile allocation and CPU separately from timing using a compatible
   profiler if available. Otherwise use isolated scalar/sequence microbenchmarks
   and temporary diagnostic counters in a separate build. Attribute scalar
   calls, conversions, array copies, callbacks and hashing. Record profiler
   availability; do not treat instrumentation timings as performance results.

Matrix: 100 (smoke), 2,000 (historical), 10,000 and 100,000 bindings; ascending,
deterministically shuffled, root-slot collision, divergence at depths 0–5,
constant hash, fixed-width strings, mixed-length byte strings and 192-byte
common-prefix strings. Run expensive constant-hash histories at 100/2,000 by
default and label omissions explicitly; do not hide their quadratic build cost.
Use at least seeds 0, 31 and one recorded additional seed.

Exit: reproducible corrected baseline; both retention policies; call-path
inventory; explicit unprofiled uncertainties. No backend optimization is
accepted using only the old checked-workload timing.

### HP1 — Realize bounded scalar operations

Dependencies: HP0. Effort: medium.

1. Add the bounded scalar layer and contracts described above. Prove chunk,
   bitmap membership/edit, rank and popcount equivalence to `HashTableBits`;
   reuse its existing rank/cardinality and bitmap-bound lemmas.
2. Prove range closure from `native_table_wf`, normalized query hashes and
   the six-level routing bound. Cover source-join paths while they remain.
3. Extract source-defined scalar control flow over small native primitives.
   Use the simple bounded popcount first. Keep any subsequent Kernighan/SWAR
   alternative separately proved and measured; it is not a prerequisite.
4. Wire only the selected native backend, and add the platform guard. Register
   new proof modules in `HASHTABLE_VFILES`, dependency rules and
   `check-hashtable-assumptions.sh`; register new OCaml modules in every native
   array test/benchmark link recipe and cleanup rules.
5. Add bytecode/native primitive comparisons to the unspecialized model:
   all 32 slots; empty/full/one-bit/two-bit patterns; random 32-bit masks;
   hashes 0 and `2^30-1`; every supported depth; raw hash extremes through the
   wrapper. Test all 16-bit words as an additional finite popcount corpus.
6. Audit generated reachable routing code for recursive number conversion or
   bit emulation. Compare HP0 measurements after this stage alone.

Exit: source refinements and assumptions pass; foreign inventory lists every
new binding; generated shape and semantic tests pass; before/after allocation
and timing identify the scalar change's contribution. Large gains are expected,
but are not a theorem or a condition for falsifying profiler evidence.

### HP2 — Remove child-list emptiness checks and redundant routing work

Dependencies: HP1. Effort: small to medium.

1. Define `pseq_is_empty` in `HashTableNative.v`, prove equivalence to the empty
   list view, and bind it to an array-length test. Extend
   `array_sequence_contract` and its view lemmas accordingly.
2. Use it in `native_children_remove`; reprove removal/refinement lemmas.
   Generated deletion must no longer call `to_list` to inspect children.
3. Carry an already computed dense rank into private replace/insert/remove
   helpers where currently recomputed. Prove agreement with existing helpers.
4. Keep checked indexing initially. Only add an option-free or unsafe primitive
   if a residual profile justifies it and occupied-slot/rank/cardinality proofs
   discharge its bound at every call. Missing-slot insertion permits index
   equal to length; replacement/removal do not.

Exit: no child-view conversion on the public removal path; contracts and old
versions pass; independent measurements for this stage.

### HP3 — Source-defined native leaf, join and collision workers

Dependencies: HP2. Effort: large; split into leaf/join and collision commits.

1. Implement native empty/leaf set/remove and native joins directly in Rocq.
   Reuse source join/refinement lemmas; construct only compact native nodes.
   Stop delegating valid public operations to `set_tree`/`remove_tree` through
   `source_of_native`/`native_of_source`. Keep conversion functions for proofs
   and test oracles in a separate extraction root if needed.
2. Retain sequence-backed collisions initially. Implement indexed source
   bucket lookup, update and removal using sequence length/get/edit. Prove
   equivalence to bucket list operations, resident-key retention, append on
   absence and empty/singleton collision normalization. Updates preserve the
   original key representative and shallow payload sharing.
3. Prove termination using a bounded index/remaining length. Inspect extraction
   for repeated linear length/view computation or large runtime fuel buildup.
   Branch width is not a collision-length bound. Use proof-erased termination
   machinery only if generated code warrants it.
4. Preserve total fallback semantics for raw modeled workers, or select new
   well-formed workers with a separately proved public bridge. Prove public
   reachability excludes any source-conversion fallback. Extend source-table
   refinement, validity, pointwise API and first-wins results.
5. Decide explicitly whether `elements` should keep its current source-tree
   conversion or use a direct proved traversal. It may materialize lists;
   enumeration allocation must still be reported separately.

Exit: public get/mem/set/remove/of_list hot paths have no reachable source-tree
round trips or `pseq_view` conversions, including constant-hash collisions.
Reference/model conversions may remain outside those paths. Full semantic
coverage includes collisions larger than 32, normalization down to one/zero,
all routing depths and retained histories.

### HP4 — Evaluate residual representation costs (conditional)

Dependencies: HP3 and a new residual profile. Effort: variable; default defer.

Only pursue if options, array copies, short construction lists or unchanged-path
copies remain material. Candidates are source-modeled singleton/pair sequence
constructors with array realizers, proved bounded access, source-defined
changed-result propagation, or a distinct branch-only sequence representation.
Keep general collision storage and the total sequence contract explicit.

Each experiment must have a model/view proof, target contract, generated audit,
finite primitive/persistence tests and an isolated measurement. A fixed array
of 32 cells can waste retained space relative to today's compact arrays; it
is not an automatic improvement. No in-place edit of published storage and no
whole-map OCaml override is authorized by this plan. Physical-identity shortcuts
would require their own one-way adequacy contract, as in Patricia, and are not
needed for HP1–HP3.

Exit: either record evidence for a selected specialization or close this stage
as deferred with the residual profile and rationale. Do not implement a second
map algorithm merely to satisfy a timing target.

### HP5 — Integrate audits, validate and publish

Dependencies: HP1–HP3, explicit HP4 decision. Effort: medium.

Extend `check-hashtable-native-array-extraction.sh` to inspect selected generated
workers and their reachable helpers. Inventory approved scalar/sequence
bindings; reject whole-operation overrides and unwanted source conversions.
Check generated public code, not only the standalone comparator. Add negative
fixtures proving the audit fails when a hot `to_list`/fallback or unapproved
override is introduced. A textual audit remains a code-shape check, not proof.

Update `check-hashtable-native-model-extraction.sh`: it currently requires
source fallback strings, which HP3 intentionally removes. Replace those checks
with direct-worker/refinement expectations instead of deleting coverage.
Retain public-interface, callback, assumption and primitive audits. Update
`hashtable-reference-release.md`, the native inventory, README and performance
note to distinguish proved models, finite tests and foreign execution.

Existing validation commands (run sequentially because extraction targets share
output directories):

```sh
make hashtable-proof hashtable-assumptions
make hashtable
make all
make hashtable-benchmark-smoke
```

`make hashtable` includes bytecode/native public, native-model, array extraction,
standalone, differential and primitive coverage. Extend that aggregate with
new scalar tests and generated audits. `make all` checks Patricia integration.
Run a clean checkout/worktree aggregate for final reproducibility rather than
relying only on cached `.vo` or generated objects. Hosted CI is separate evidence.

Proposed new targets: `hashtable-performance-baseline`,
`hashtable-performance-matrix`, `hashtable-scalar-test`,
`hashtable-scalar-test-native`, `hashtable-hot-path-audit`. They do not exist yet;
implement/document their arguments during the relevant stages. CI should run
correctness/audit/small workload smoke, not enforce noisy wall-clock thresholds.

## Acceptance and stopping rules

Correctness is mandatory: all proofs and audits, raw-hash extremes, custom
equivalence, representative retention, duplicate bulk input, arbitrary values,
multiple functor instances/seeds and old-version tests pass. No admitted
obligations or new axioms; any new explicit primitive hypotheses are inventoried.

Performance evaluation uses HP0's corrected paired baseline on the same machine.
Initial engineering targets: at least 10x lower generated build allocation on
the two historical distributions, ordinary-workload median time within 2x of
the standalone HAMT, and no unexplained retained-heap growth above 5% with
identical root histories. These are proposed targets, not observed results or
promises. Report every operation and distribution; collision-heavy results
are separate and cannot be averaged away.

Investigate repeatable regressions above 10% in time or allocation; repeat
timings only to resolve noise or a changed implementation. Semantic changes
cannot be accepted in exchange for speed. If HP1–HP3 miss targets, publish the
remaining costs and decide HP4 from evidence. A correct useful improvement can
be delivered with explicitly unmet targets; do not label performance parity
achieved. No requirement to beat mutable `Hashtbl` or every Patricia/AVL case.

Stage order: HP0 → HP1 → HP2 → HP3 → HP4 decision → HP5. Keep stages independently
reviewable and measurements associated with each revision. If an optimization
fails its gate, retain the last validated implementation and record the failed
experiment; the completed correctness release remains a separate milestone.
