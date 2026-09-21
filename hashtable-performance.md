# Hash-table performance observations

This note records local, workload-specific measurements and optimization
ideas. It is not a complexity proof, a portable benchmark result, or a claim
about an unmeasured OCaml runtime.

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

The HAMT commands use `ocamlopt`, 2,000 ascending bindings, seed 31, and keep
every prefix version of each persistent map. Each timed operation checks its
result against an association-list oracle. The Patricia command uses a separate
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
- Patricia is currently the stronger persistent implementation for ordinary
  integer and string lookup/removal workloads, and for many structural unions.
- AVL uses less retained memory than Patricia and is a steadier choice when
  comparator-based semantics or long common-prefix string behavior matter.
- The public HAMT has the desired generated/refined implementation boundary,
  but its current target realization needs performance work before it should be
  selected for throughput.

## Likely public-HAMT cost centers

These are hypotheses from the allocation profile and implementation shape, not
yet profiler-confirmed causes.

1. `HashTablePrimitives.insert`, `replace`, and `remove` allocate a fresh array
   for every compact-child edit. Fresh storage is required by the persistent
   sequence contract, but the number and placement of those edits should be
   measured.
2. The generated representation crosses the `pseq` extraction boundary for
   every compact-child operation. Construction, option values, and callback
   wrappers may add temporary allocation beyond the final map structure.
3. `pseq_view` is extracted as `Array.to_list`; enumeration necessarily
   materializes a list. It should remain confined to enumeration, but profiling
   must verify that an unexpected call path does not reach it during updates or
   lookup.
4. The benchmarks deliberately retain every prefix. This is valuable
   persistence coverage but magnifies allocation behavior and does not model a
   workload that discards intermediate roots.

## Optimization plan

1. **Profile before changing the representation.** Run `memtrace` or a sampled
   allocation profiler for build, lookup, update, and removal. Attribute
   allocation to generated workers, primitive edits, option/list construction,
   and hashing. Repeat with retained-prefix and latest-version-only histories.
2. **Add fairer benchmark distributions.** Record several sizes, random input,
   `root-slot-collision`, collision-heavy custom keys, and long-prefix strings.
   Run multiple repetitions and report median/range instead of interpreting one
   timing as a stable ranking.
3. **Specialize the compact sequence representation.** A persistent,
   fixed-width (at most 32 children) node representation can copy only its
   occupied child storage and avoid generic list/option scaffolding. It must
   preserve the `HashTableArrayRefinement.v` view and fresh-update contract.
4. **Reduce temporary values in generated hot paths.** Inspect the extracted
   `native_get`, `native_set`, and `native_remove` workers after profiling.
   Candidate changes include direct bounded-index helpers and extraction
   directives for hot sequence combinators. Keep `pseq_view` materialization
   limited to `elements`.
5. **Consider a reviewed specialized target realizer.** If extraction-level
   specialization is insufficient, implement a small OCaml compact-node
   realizer behind the existing abstract `HashMap` interface, prove it meets
   the quantified sequence contract, and extend the extraction/backend audits
   and bytecode/native differential suites. Do not trade persistence or the
   documented foreign-boundary checks for a benchmark result.
6. **Re-evaluate the public backend only with evidence.** Compare the revised
   generated HAMT against the standalone HAMT, Patricia, AVL, and `Hashtbl` on
   matched integer/string workloads. Publish allocation, retained heap, and
   timing together.

