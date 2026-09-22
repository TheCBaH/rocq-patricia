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
includes an association-list oracle search inside the timer; string lookup
compares directly with expected values. Update/remove validation is outside the
timer. The Patricia command uses a separate
`ocamlopt` harness with 10,000 bindings per input tree and includes more
operations, randomized insertion, and several string distributions. Therefore
the two tables below must not be used to compare a HAMT number directly with a
Patricia number.

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
  lookup/removal and structural-union workloads. Its ranking against HAMT
  still needs a matched harness.
- AVL uses less retained memory than Patricia and is a steadier choice when
  comparator-based semantics or long common-prefix string behavior matter.
- The public HAMT has the desired generated/refined implementation boundary,
  but its current target realization needs performance work before it should be
  selected for throughput.

## Cost centers identified by source inspection

These call paths exist in the source and regenerated OCaml. Their share of
runtime/allocation still requires profiling or controlled experiments.

1. `HashTableNativeArrayExtract.v` realizes arrays but supplies no HAMT scalar
   bindings. Generated `HashTableBits.chunk`, `rank` and bitmap edits reach
   recursive `BinNat.N`/`BinPos.Pos` operations. `N.of_nat` recursively converts
   depth arithmetic, `N.shiftr` iterates division, and `popcount32` always makes
   32 steps. Mapping the number types to OCaml `int` does not make all these
   operations native instructions. This is the first optimization candidate,
   following `PatriciaExtract.v`'s scalar-realizer precedent.
2. `native_children_remove` materializes `pseq_view children'` just to test
   emptiness. `native_get` materializes collision entries for `bucket_get`.
   `native_set`/`native_remove` delegate non-branch cases through
   `source_of_native`, source workers and `native_of_source`, constructing
   temporary nodes/lists. Thus enumeration-only materialization is a goal,
   not the current generated backend's behavior.
3. The standalone HAMT uses the same `HashTablePrimitives` array edits and is
   much cheaper on these workloads. Fresh compact-array copies are real costs,
   but do not by themselves explain the generated backend's allocation gap.
   Both implementations already copy only occupied child storage.
4. Option/callback allocation, repeated rank computation and copied unchanged
   paths remain secondary candidates. Measure them after scalar realization.
   Branch children have width at most 32; collision sequences do not.

The current enumeration-only audit in
`check-hashtable-native-array-backend.sh` examines the standalone
`HashMapNative.ml`, not the generated workers. The generated extraction audit
checks primitive/worker presence, not the absence of these hot call paths.

On 2026-09-22, rerunning both HAMT benchmark targets with Rocq 9.2 and OCaml
4.14.3 reproduced the recorded build allocations exactly: integer public/
standalone 215,905,264 / 1,394,040 bytes; string 243,088,456 / 1,279,488 bytes.
Integer build was 8.056 / 0.302 ms and string build 9.190 / 0.360 ms in this
single rerun. This confirms the baseline issue, not its allocation attribution
or a stable speed ratio. No optimized implementation was measured.

## Optimization plan

1. Correct timing boundaries and add matched, repeated workloads; profile the
   existing backend with history policies measured separately.
2. Add bounded scalar realizers with range contracts and source-defined
   popcount/control flow, following the Patricia extraction approach.
3. Add a sequence emptiness primitive, direct native leaf/join workers, and
   indexed collision workers, proving refinement before selecting each worker.
4. Audit the generated public call graph and primitive contracts; run existing
   bytecode/native, persistence, representative and callback suites.
5. Consider additional sequence specialization only if the residual profile
   warrants it. A Rocq theorem quantified over a sequence contract does not
   itself prove that handwritten OCaml satisfies that contract; target execution
   remains an explicit foreign obligation unless separately verified.
6. Re-evaluate against the standalone HAMT, Patricia, AVL and `Hashtbl` on the
   same workloads. Keep the public API and persistence contract unchanged.

Execution details and closure criteria are in
[the performance plan](hashtable-performance-plan.md). There is no promised
speedup or change to the completed H0–H5 correctness gates in this proposal.
