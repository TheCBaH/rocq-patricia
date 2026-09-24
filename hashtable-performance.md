# Hash-table performance observations

This note records local, workload-specific measurements and optimization
ideas. It is not a complexity proof, a portable benchmark result, or a claim
about an unmeasured OCaml runtime.

Feasibility review: 2026-09-22. The proposed optimization is feasible, with a
smaller first step than a new node representation: realize bounded scalar
operations natively, then remove source/list conversions from hot workers.
The [detailed implementation plan](hashtable-performance-plan.md) records the
evidence, proof/foreign boundary, dependencies and acceptance gates;
[the performance tracker](hashtable-performance-todo.md) owns progress.
The [matched matrix report](hashtable-performance-results.md) summarizes the
final clean `bccd2a9` 228-record, seven-repetition five-way result and links
its raw JSONL archive alongside the original corrected baseline.

## Implementation status

The first three implementation stages are now present in the generated public
backend. `HashTableNativeBits.v` supplies source-defined bounded chunk,
bitmap-membership/edit, and rank operations, and
`HashTableNativeArrayExtract.v` realizes them through checked OCaml scalar
bindings. `native_get`, `native_set`, and `native_remove` use those bindings;
the primitive corpus covers their target domains. Source theorems establish
scalar-domain closure for public lookup, set/remove, direct joins, and
first-wins loading under wrapper-normalized hashes and the standard valid-table
premises. This is not a claim that the foreign OCaml realization has become
kernel-checked.

The public native get/set/remove/first-wins-load workers now operate directly
on native constructors. They use bounded indexed collision sequences and a
direct native join worker; generated hot-path audits reject source-tree and
sequence-view conversion there. `elements` intentionally remains the sole
source-tree conversion: enumeration materializes a list by design and its
allocation is measured separately. Bytecode/native model tests cover 40/41
entry constant-hash buckets, singleton/empty normalization, divergence at
routing depths 0–5, and retained versions.

The collision get/set/remove source workers have separately stated foreign
array-view contracts. Their target adapter performs one bounded scan over the
private array, then a fresh copy for a changed bucket. Generated binding
audits and finite adapter tests cover this extraction boundary; the source
worker refinements remain kernel-checked. Long collision removal still copies
the shrinking array, unlike the handcoded HAMT's list bucket.

Storage specialization is deliberately deferred. The remaining smoke gap to
the standalone backend has not been attributed sufficiently among callbacks,
checked options, and fresh compact-array copies to justify a fixed-width or
unsafe-index representation. The full rationale and open proof/measurement
work are tracked in HP1, HP2, HP4, and HP5 rather than implied by these local
measurements.

## Implementations

| Name | Implementation | Persistence |
| --- | --- | --- |
| Public HAMT | `HashMap.Make`, backed by the generated `HashTableNative` workers and `HashTablePrimitives` | Yes |
| Standalone array HAMT | `HashMapNative.Make` | Yes |
| AVL | `Stdlib.Map.Make` | Yes |
| Imperative table | `Stdlib.Hashtbl` | No |
| Patricia | `PatriciaMap` / `StringPatriciaMap` | Yes |

The public and standalone HAMTs are intentionally separate implementations.
The public HAMT is the supported generated backend; the standalone array HAMT
is retained as a comparison implementation and test oracle.

## Measurements recorded on 2026-09-21

Commands:

```sh
make hashtable-benchmark hashtable-string-benchmark
make benchmark
```

The HAMT commands use `ocamlopt`, 2,000 ascending bindings and seed 31. Separate
retained-heap passes keep every prefix version of each persistent map; the timed
build/update/remove passes do not retain every intermediate root. Integer lookup
and string lookup both compute only an observable checksum during timing; their
independent expected-result checks run afterward. Update/remove validation is
also outside the timer. The Patricia command uses a separate
`ocamlopt` harness with 10,000 bindings per input tree and includes more
operations, randomized insertion, and several string distributions. Therefore
the two tables below must not be used to compare a HAMT number directly with a
Patricia number. `make patricia-matrix-benchmark` and
`make patricia-string-matrix-benchmark` now provide separate process-level
integer and string companions with the HAMT harnesses' exact input, operation,
retention, warmup/repetition, and JSONL metadata boundaries. The matrix runner
pairs these files by workload, size, and seed because the two un-namespaced
generated extraction trees cannot link in one executable. The full repeated
size matrix is recorded in the matched matrix report. The historical tables
still use a different harness boundary.

The matrix records post-GC retained heap at the 100 and 2,000 representative
sizes, including capped collision histories. Its 10,000 and 100,000 records
explicitly set `live_heap: false`: they retain the complete timed
operation/allocation and semantic-validation boundary without repeatedly
constructing a separate large retained history for every distribution.

### Generated HAMT, standalone HAMT, AVL, and imperative table

Times are complete checked workloads, not per-operation latency.

| Integer workload, 2,000 bindings | Public HAMT | Standalone HAMT | AVL | `Hashtbl` |
| --- | ---: | ---: | ---: | ---: |
| Build | 7.927 ms | 0.305 ms | 0.121 ms | 0.040 ms |
| Lookup | 12.589 ms | 9.495 ms | 9.204 ms | 9.093 ms |
| Update | 6.955 ms | 0.382 ms | 0.206 ms | 0.145 ms |
| Remove | 6.773 ms | 0.274 ms | 0.092 ms | 0.065 ms |

| Fixed-width string workload, 2,000 bindings | Public HAMT | Standalone HAMT | AVL | `Hashtbl` |
| --- | ---: | ---: | ---: | ---: |
| Build | 9.471 ms | 0.399 ms | 0.201 ms | 0.053 ms |
| Lookup | 4.809 ms | 0.161 ms | 0.151 ms | 0.069 ms |
| Update | 7.810 ms | 0.318 ms | 0.185 ms | 0.085 ms |
| Remove | 8.350 ms | 0.327 ms | 0.113 ms | 0.062 ms |

The public HAMT retained about the same heap as the standalone HAMT: 1,258,928
versus 1,258,872 bytes for the integer prefix history, and 1,166,360 versus
1,166,376 bytes for the string history. Its transient allocation was much
higher: 215,905,264 versus 1,394,040 bytes for integer build, and 243,088,456
versus 1,279,488 bytes for string build. The corresponding AVL build
allocation was 1,244,688 bytes and the imperative-table allocation was 80,568
bytes for both workloads.

**Observation:** the current public generated HAMT is not competitive for
throughput-sensitive use. The retained-heap figures show that its large cost is
mostly temporary allocation, not the memory required to retain the versions.
The standalone HAMT is far closer to AVL for build, update, and removal, while
the imperative table is fastest when persistence is unnecessary.

### Patricia, AVL, and imperative table

The following selected results come from the separate 10,000-binding Patricia
harness. As above, times are complete workloads.

| Integer workload | Patricia | AVL | `Hashtbl` |
| --- | ---: | ---: | ---: |
| Build | 0.866 ms | 1.577 ms | 0.162 ms |
| Lookup | 1.168 ms | 2.468 ms | 0.464 ms |
| Update | 0.761 ms | 1.390 ms | 0.307 ms |
| Remove | 0.306 ms | 0.821 ms | 0.332 ms |

| Three-character string workload | Patricia | AVL | `Hashtbl` |
| --- | ---: | ---: | ---: |
| Build | 0.696 ms | 1.726 ms | 0.204 ms |
| Lookup | 1.981 ms | 2.625 ms | 0.631 ms |
| Update | 2.000 ms | 1.576 ms | 0.399 ms |
| Remove | 0.480 ms | 0.745 ms | 0.393 ms |

For the measured persistent maps, Patricia retained about 8 words per binding,
while AVL retained about 6. Patricia generally beat AVL for integer lookup,
membership, removal, and structural unions. It lost on randomized string
builds and some string updates. With 192-byte common-prefix strings, Patricia
and the imperative table had similar lookup times, while Patricia's
overlap/equal union was substantially slower than AVL because prefix inspection
dominates that distribution.

## Current interpretation

- Use `Hashtbl` for the fastest mutable single-version table. It does not offer
  retained versions or persistent structural sharing.
- Patricia performs well against AVL in its measured integer/string
  lookup/removal and structural-union workloads. The matched repeated matrix
  now gives direct operation comparisons with HAMT on the planned inputs.
- AVL uses less retained memory than Patricia and is a steadier choice when
  comparator-based semantics or long common-prefix string behavior matter.
- The public HAMT has the desired generated/refined implementation boundary,
  but its current target realization needs performance work before it should be
  selected for throughput.

## Cost centers and residual uncertainty

The following separates implemented removals from costs that still need
attribution. A passing extraction audit establishes code shape, not an OCaml
cost model.

1. Scalar routing, child emptiness, collision lookup/update/removal, and
   distinct-hash joins no longer use their former recursive arithmetic or
   source/view fallbacks in public workers. The isolated primitive benchmark is
   useful attribution evidence, but does not count calls within a map update.
2. The standalone HAMT uses the same `HashTablePrimitives` array edits and is
   much cheaper on these workloads. Fresh compact-array copies are real costs,
   but do not by themselves explain the generated backend's allocation gap.
   Both implementations already copy only occupied child storage.
3. Callback costs, checked-option allocation, and copied unchanged paths remain
   possible contributors. Branch children have width at most 32; collision
   sequences do not, so a branch-only storage experiment cannot safely change
   the general sequence contract.

`check-hashtable-native-array-backend.sh` continues to audit the standalone
implementation. The companion generated extraction audit now rejects
source-tree and sequence-view conversion in the public native workers, and its
negative fixtures prove that injected conversion or a nonrecursive whole-map
override is rejected.

The historical 2,000-binding figures above predate the corrected operation
boundary and direct workers; they are retained only as a baseline record. After
the direct-worker change, the corrected 100-binding integer smoke measured
public/standalone first-wins build allocation of 124,272 / 40,376 bytes and
public existing/new set allocation of 182,920 / 213,040 bytes. The string
smoke reports the same operation separation for fixed-width, mixed-length, and
common-prefix keys. These are single local smoke points, not a portable
speedup claim or the required repeated, matched Patricia matrix. The capped
2,000-entry constant-hash point and primitive measurements are recorded in the
tracker.

The matrix also has deterministic positive-integer `divergence-depth-0` through
`divergence-depth-5` inputs: the HAMT callback hashes them so every routing
chunk before the named depth agrees. Their paired Patricia records use the
identical keys. These distributions are capped at 100/2,000 bindings, like the
constant-hash workload, because the later depths have a small remaining hash
domain and would otherwise create large collision histories.

## Optimization plan

1. Obtain whole-map attribution for the residual generated lookup/update
   allocation and reconstruct a corrected pre-optimization comparison if an
   exact historical scalar-stage speedup claim is needed.
2. Keep the completed public scalar range proofs and record any isolated
   scalar-stage measurement separately from the current full matrix.
3. Retain the proved indexed sequence and direct workers; no source/view
   conversion remains in the public hot set.
4. Keep generated public-call audits, their negative fixtures, and bytecode/
   native model suites in the release evidence.
5. Consider additional sequence specialization only if the residual profile
   warrants it. A Rocq theorem quantified over a sequence contract does not
   itself prove that handwritten OCaml satisfies that contract; target execution
   remains an explicit foreign obligation unless separately verified.
6. Re-evaluate against the standalone HAMT, Patricia, AVL and `Hashtbl` on
   identical workloads. Keep the public API and persistence contract unchanged.

Execution details and closure criteria are in
[the performance plan](hashtable-performance-plan.md). There is no promised
speedup or change to the completed H0–H5 correctness gates in this proposal.
