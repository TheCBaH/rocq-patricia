# Patricia benchmark results

Run date: 2026-08-29  
Command: `make -C patricia benchmark`  
Platform: aarch64 Linux 7.0.0-28-generic; OCaml 4.14.3 native code.

## Result

The current benchmark completed with `Patricia comparison benchmark: ok`.
It compares the extracted integer and direct-string Patricia trees with
`Stdlib.Map` (OCaml's balanced AVL implementation). Every measured map is
checked against the corresponding AVL map before its result is reported.

The main current result is that specialized native `union_left` shares
one-sided subtrees and joins disjoint inputs directly. Across the 10,000 to
1,000,000-binding runs below, disjoint-union allocation stayed below 500 words
for both Patricia variants, while AVL allocation rose from 2,404 to 4,940
words. Half-overlapping union is also substantially less allocating than AVL.
The shortest union times are near the resolution of `Unix.gettimeofday`;
allocation is the more dependable signal for those operations.

These are measurements from one machine, not complexity proofs or regression
thresholds.

## Workloads and method

The source is [`PatriciaBenchmark.ml`](PatriciaBenchmark.ml). It uses the
default `PATRICIA_BENCH_SIZE=10000`, so each input map has 10,000 bindings.

- Integer keys are consecutive positive OCaml integers. String keys are
  fixed-width base-62 strings of lengths 3, 4, and 5.
- Build, lookup (three complete passes), add fresh keys, update existing keys,
  and remove all keys are timed independently.
- A disjoint left-biased union joins ranges `[1, n]` and `[n+1, 2n]`; the
  overlap workload joins `[1, n]` and `[n/2+1, 3n/2]`. Both use
  `union_left`; the expected binding counts are checked.
- Retained size is measured after a major collection and compaction.
  Allocation is the OCaml GC minor-plus-major word counter. The operation
  timings include their benchmark loop and are reported per key except for
  unions, which are one operation.

## Measurements

All allocation and retained-size figures are OCaml heap words. Times are a
single run; `0.000 ms` means that the measured interval rounded to zero at the
clock precision, not that the operation took no time.

### Integer keys

| Operation | Patricia | Stdlib.Map | Patricia allocation | AVL allocation |
| --- | ---: | ---: | ---: | ---: |
| Build | 0.663 ms | 1.423 ms | 465,632 | 973,858 |
| Retained map size | 8.00 words/binding | 6.00 words/binding | 79,991 | 59,999 |
| Lookup | 41.0 ns/op | 82.9 ns/op | 60,043 | 60,043 |
| Add fresh keys | 42.2 ns/op | 159.3 ns/op | 507,582 | 1,087,954 |
| Update existing keys | 78.6 ns/op | 126.5 ns/op | 769,164 | 785,116 |
| Remove keys | 22.3 ns/op | 79.9 ns/op | 308,608 | 433,420 |
| Disjoint left-biased union | 0.001 ms | 0.004 ms | 288 | 2,404 |
| 50%-overlapping left-biased union | 0.018 ms | 0.104 ms | 243 | 81,324 |

### String keys

| Key length | Build P / AVL (ms) | Lookup P / AVL (ns/op) | Add P / AVL (ns/op) | Update P / AVL (ns/op) | Remove P / AVL (ns/op) |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3 | 0.754 / 1.578 | 62.5 / 80.2 | 100.6 / 157.6 | 121.3 / 130.9 | 40.1 / 72.8 |
| 4 | 0.801 / 1.429 | 66.6 / 78.9 | 98.9 / 143.2 | 115.0 / 125.1 | 40.0 / 69.5 |
| 5 | 0.890 / 1.555 | 63.1 / 81.1 | 105.5 / 158.3 | 112.1 / 131.4 | 41.7 / 70.1 |

| Key length | Retained P / AVL (words/binding) | Disjoint union P / AVL (ms) | Disjoint allocation P / AVL | Overlap union P / AVL (ms) | Overlap allocation P / AVL |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3 | 8.00 / 6.00 | 0.000 / 0.003 | 351 / 2,404 | 0.045 / 0.070 | 40,330 / 81,324 |
| 4 | 8.00 / 6.00 | 0.001 / 0.003 | 351 / 2,404 | 0.049 / 0.072 | 40,330 / 81,324 |
| 5 | 8.00 / 6.00 | 0.000 / 0.003 | 351 / 2,404 | 0.056 / 0.068 | 40,330 / 81,324 |

The string build allocations were 726,896 words for Patricia and 973,858 for
AVL at every tested length. Patricia allocation for string add, update, and
remove was respectively 772,433, 923,171, and 441,976 words; the AVL figures
were 1,087,954, 785,116, and 433,420 words.

## Scaling with tree size

The following additional runs completed with the same result checks:

```sh
PATRICIA_BENCH_SIZE=100000 make -C patricia benchmark
PATRICIA_BENCH_SIZE=1000000 PATRICIA_BENCH_STRING_LENGTHS=4,5 \\
  make -C patricia benchmark
```

The string scaling table uses four-character keys at every size, avoiding a
key-length change as a confounding factor. Three-character keys cannot hold
the two disjoint one-million-key inputs. Each table entry is Patricia / AVL.

### Integer keys

| Bindings per input | Build (ms) | Lookup (ns/op) | Retained words/binding | Disjoint union (ms) | Disjoint allocation | 50%-overlap union (ms) | Overlap allocation |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10,000 | 0.663 / 1.423 | 41.0 / 82.9 | 8.00 / 6.00 | 0.001 / 0.004 | 288 / 2,404 | 0.018 / 0.104 | 243 / 81,324 |
| 100,000 | 8.484 / 16.455 | 43.6 / 103.0 | 8.00 / 6.00 | 0.002 / 0.007 | 379 / 3,620 | 0.251 / 1.780 | 365 / 965,872 |
| 1,000,000 | 111.533 / 196.015 | 48.8 / 122.1 | 8.00 / 6.00 | 0.007 / 0.010 | 486 / 4,940 | 3.211 / 25.025 | 470 / 10,193,264 |

### Four-character string keys

| Bindings per input | Build (ms) | Lookup (ns/op) | Retained words/binding | Disjoint union (ms) | Disjoint allocation | 50%-overlap union (ms) | Overlap allocation |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10,000 | 0.801 / 1.429 | 66.6 / 78.9 | 8.00 / 6.00 | 0.001 / 0.003 | 351 / 2,404 | 0.049 / 0.072 | 40,330 / 81,324 |
| 100,000 | 9.707 / 17.163 | 73.5 / 101.5 | 8.00 / 6.00 | 0.002 / 0.007 | 406 / 3,620 | 0.520 / 1.498 | 400,347 / 965,872 |
| 1,000,000 | 106.824 / 191.229 | 82.7 / 126.8 | 8.00 / 6.00 | 0.004 / 0.011 | 405 / 4,940 | 5.882 / 25.838 | 4,000,362 / 10,193,264 |

The retained representation remains exactly 8 Patricia words per binding and
6 AVL words per binding. Lookup cost rises moderately over the 100-fold size
increase: from 41.0 to 48.8 ns for integer Patricia and from 66.6 to 82.7 ns
for four-character string Patricia. The AVL lookup increase is larger in this
sample (82.9 to 122.1 ns and 78.9 to 126.8 ns respectively), but these three
points are not an asymptotic proof.

The disjoint-union allocation stays effectively constant over this range,
which is consistent with a direct join that reuses both input subtrees. Integer
half-overlap also stays below 500 words: on these ordered ranges, the native
algorithm can share both the left map and the right map's disjoint tail rather
than rebuilding their bindings. The string half-overlap allocation grows with
the input size, but remains about 39% of the AVL allocation at one million
bindings. Timings grow with size for the overlap cases, as expected for work
that must inspect or retain those bindings. This is empirical behavior of
these inputs, not a machine-independent complexity guarantee.

## Current implementation boundary

The benchmark measures the optimized native extraction, not only the pure
Rocq definitions. [`PatriciaExtract.v`](PatriciaExtract.v) replaces both
proof-side fuelled `combine` functions with direct structural OCaml recursion.
It also provides specialized native `union_left` functions: empty or
unchanged one-sided subtrees are reused, disjoint prefixes are joined
immediately, and only a potentially overlapping route is rebuilt.
`union_right` reverses the arguments.

Those extraction overrides explain the small disjoint-union allocation and
the lower allocation of the overlapping workloads. Their equivalence to the
fuelled Rocq definitions is a trusted refinement boundary; the benchmark and
its AVL equivalence checks are executable validation, not a proof of that
refinement or of asymptotic cost.

## Reproducing or varying the run

```sh
make -C patricia benchmark

PATRICIA_BENCH_SIZE=100000 make -C patricia benchmark
PATRICIA_BENCH_SIZE=1000000 PATRICIA_BENCH_STRING_LENGTHS=4,5 \\
  make -C patricia benchmark
```

`PATRICIA_BENCH_STRING_LENGTHS` selects a comma-separated non-empty list of
positive string lengths. Select longer keys when the requested size exceeds a
shorter base-62 key space; the default three-character workload can hold at
most 119,164 bindings per input map because the benchmark also constructs its
disjoint companion range.
