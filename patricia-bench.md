# Patricia benchmark results

- Run date: 2026-08-29
- Last reviewed: 2026-08-31
- Command: `make -C patricia benchmark`
- Platform: aarch64 Linux 7.0.0-28-generic; OCaml 4.14.3 native code

This document is the measurement record and reproduction guide. Performance
analysis is in [`patricia-str.md`](patricia-str.md), and all current or proposed
work is tracked in [`patricia-todo.md`](patricia-todo.md).

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
Short union timings are now batched and sampled, but allocation remains the
more dependable signal for tiny operations.

These are measurements from one machine, not complexity proofs or regression
thresholds.

### Small-operation follow-up

A later 10,000-binding run added checked mixed hit/miss membership and
`elements` workloads after implementing direct `mem` traversal and
accumulator-based traversal in both source models. A subsequent run added
failed deletion after implementing identity-preserving `remove`. The fixed 61-word
membership figure is benchmark overhead across 60,000 operations; unlike
`get`, membership no longer allocates an `option` per hit. `elements`
allocation is linear in its 10,000-pair result list and matches
`Stdlib.Map.bindings` in this run. Each failed-deletion workload repeatedly
uses one just-outside key, verifies the returned Patricia root with OCaml
physical identity, and allocates only the fixed 26-word measurement overhead.

| Key/workload | Patricia time | AVL time | Patricia allocation | AVL allocation |
| --- | ---: | ---: | ---: | ---: |
| Integer membership | 24.0 ns/op | 85.3 ns/op | 61 | 61 |
| Integer `elements` | 3.8 ns/binding | 2.5 ns/binding | 60,026 | 60,026 |
| 4-character membership | 63.1 ns/op | 79.8 ns/op | 61 | 61 |
| 4-character `elements` | 2.9 ns/binding | 2.4 ns/binding | 60,026 | 60,026 |
| Integer absent removal | 12.3 ns/op | 88.2 ns/op | 26 | 26 |
| 4-character absent removal | 17.1 ns/op | 84.4 ns/op | 26 | 26 |

The source-level `Some changed` signal adds an option block at each rebuilt
level of a successful deletion. In the same run, removing every present key
allocated 452,101 words for integer Patricia and 588,290 words for string
Patricia, compared with 308,608 and 441,976 in the earlier table below. A
future extraction refinement could use physical child identity as the native
change signal, but this implementation deliberately does not widen the trusted
extraction boundary for that tradeoff.

## Workloads and method

The source is [`PatriciaBenchmark.ml`](PatriciaBenchmark.ml). It uses the
default `PATRICIA_BENCH_SIZE=10000`, so each input map has 10,000 bindings.

- Integer keys are consecutive positive OCaml integers. String keys are
  fixed-width base-62 strings of lengths 3, 4, and 5.
- Each build is also repeated after a deterministic Fisher--Yates permutation
  of the same keys, separating insertion-order effects from key-set effects.
- Lookup (three complete passes), add fresh keys, update existing keys, remove
  one absent key repeatedly, and remove all keys are timed independently. A
  mixed trace additionally interleaves successful and failed lookups and
  removals with existing-key updates and fresh insertions.
- Membership alternates complete passes over present and disjoint absent keys;
  `elements` is checked against the corresponding AVL bindings.
- Generic combine is measured in both leaf/tree orientations. Its function
  transforms every one-sided value and deletes the overlapping binding; full
  bindings are checked against `Stdlib.Map.merge`.
- A disjoint left-biased union joins ranges `[1, n]` and `[n+1, 2n]`; the
  overlap workload joins `[1, n]` and `[n/2+1, 3n/2]`. Both use
  `union_left`; the expected binding counts are checked. Equal, subset, no-op,
  and sparse-overlap inputs complement those two baseline shapes. Current union
  rows are per-union medians from five samples; batches contain 32 unions up to
  100K bindings and one union above that threshold. Set
  `PATRICIA_BENCH_SHORT_SAMPLES` and `PATRICIA_BENCH_SHORT_BATCH` to override
  those positive defaults.
- An adversarial string family shares a 192-byte prefix and differs only in a
  four-character suffix. Set `PATRICIA_BENCH_LONG_PREFIX_LENGTH` to a
  non-negative prefix length; zero removes the common prefix while retaining
  the same workload shape.
- Retained size is measured after a major collection and compaction.
  Allocation is the OCaml GC minor-plus-major word counter. The operation
  timings include their benchmark loop and are reported per key except for
  unions, which are one operation.

## Measurements

All allocation and retained-size figures are OCaml heap words. Historical
tables below used one timing run; current union rows report a batched-sample
median and min--max range. `0.000 ms` means that the displayed interval rounded
to zero at the clock precision, not that the operation took no time.
These tables are the pre-bounded-scanner baseline; the completed follow-up and
fresh 10K/100K overlap measurements appear below.

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

## Baseline scaling with tree size

The following pre-bounded-scanner runs completed with the same result checks:

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

These baseline results retained exactly 8 Patricia words per binding and
6 AVL words per binding. Lookup cost rises moderately over the 100-fold size
increase: from 41.0 to 48.8 ns for integer Patricia and from 66.6 to 82.7 ns
for four-character string Patricia. The AVL lookup increase is larger in this
sample (82.9 to 122.1 ns and 78.9 to 126.8 ns respectively), but these three
points are not an asymptotic proof.

The disjoint-union allocation stayed effectively constant over this range,
which is consistent with a direct join that reuses both input subtrees. Integer
half-overlap also stays below 500 words: on these ordered ranges, the native
algorithm can share both the left map and the right map's disjoint tail rather
than rebuilding their bindings. The string half-overlap allocation grows with
the input size, but remains about 39% of the AVL allocation at one million
bindings. Unlike the integer result, however, its near-exact progression from
40,330 to 400,347 to 4,000,362 words shows a residual allocation proportional
to the number of compared string branches. Timings grow with size for the
overlap cases. This is empirical behavior of these inputs, not a
machine-independent complexity guarantee.

## Benchmark-driven implementation results

### 1. Bounded, allocation-free `agrees_before` completed

The previous extracted `StringBits.agrees_before` called `first_diff`, which
scanned until the first difference and returned `Some differing`; the caller
only needed a Boolean answer about positions before the current split. On
identical or deeply shared prefixes that performed unnecessary scanning and
created a short-lived option value at each compared branch.

The allocation sequence above is the signature of that path: approximately
four words per binding while the physical-identity checks ultimately return
the already existing left subtree. A temporary, uncommitted generated-code
experiment replaced it with a closed tail-recursive byte scan that:

- compares only bytes strictly before `split >> 4`;
- masks the relevant high bits of the final byte for tags 1 through 8; and
- returns `bool` directly, without calling `first_diff`.

`StringBits.v` now defines the bounded worker, proves its exact prefix
specification, and proves it equal to logical `agrees_before`. String combine
uses that source function. Its packed native realization is a closed
tail-recursive byte scan, so calls do not allocate a closure or an option.
The exhaustive oracle checks every one-byte pair at every valid packed split.

Fresh checked results are:

| Four-character bindings per input | Before time / allocation | Bounded time / allocation | AVL time / allocation |
| ---: | ---: | ---: | ---: |
| 10,000 | 0.049 ms / 40,330 words | 0.051 ms / 128 words | 0.089 ms / 81,324 words |
| 100,000 | 0.520 ms / 400,347 words | 0.532 ms / 143 words | 1.615 ms / 965,872 words |
| 1,000,000 | 5.882 ms / 4,000,362 words | 7.169 ms / 113 words | 23.891 ms / 10,193,264 words |

The before and bounded runs were separate executions, so their single-run
timing differences are noise-level observations. The reduction from
per-binding to fixed measurement-sized allocation is the dependable result;
the one-million rerun confirms it beyond the original 10K and 100K evidence.
The packed-position relation remains part of the already documented native
extraction boundary; the bounded algorithm itself now has a source definition
and equivalence proof.

### 2. Accumulator-based `elements` completed

Both tree modules previously computed:

```coq
elements left ++ elements right
```

`++` copied the complete left result at every branch. Both implementations now
use `elements_aux tree tail`. `elements_aux_spec` recovers the append law used
by the existing fold, soundness, completeness, and uniqueness proofs, and the
benchmark checks the resulting bindings. The follow-up table above records
linear output-list allocation at 10,000 bindings.

### 3. Absent-removal identity completed

Both maps now use `remove_changed`, where `None` reports an absent key and
`Some tree` carries a real deletion. `remove_absent_identity` proves that a
failed deletion returns the original source tree, while the existing lookup
and well-formedness laws are retained. The native benchmark checks physical
root identity and fixed allocation after 10,000 failed deletions.

The benchmark already has a separate `update keys` case that replaces and
checks every existing binding. An optional `set_if_changed`/`update` API
supplied with value equality could additionally avoid rebuilding an existing
binding whose value is unchanged. This remains relevant to persistent compiler
data-flow maps, where converged updates are common. It is tracked as optional
runtime work under N5 in `patricia-todo.md`.

### 4. Generic-combine leaf cases completed

For an overlapping leaf/tree pair, native `combine` previously mapped the
whole tree and then called `remove` or `set` for the leaf key. Both maps now
provide proved source-level `combine_leaf_left` and `combine_leaf_right`
workers. A key-aware `map_filter` performs the overlapping transformation or
deletion during the required mapping pass, eliminating the subsequent
replacement path. The absent-key branch retains mapped-tree insertion.

The checked workload transforms all one-sided values and deletes one
overlapping binding. Allocation is deterministic in these runs; the individual
sub-millisecond timings are too noisy to support a speedup claim.

| 10K workload | Before | Fused | Reduction |
| --- | ---: | ---: | ---: |
| Integer leaf/tree | 120,128 words | 120,027 words | 101 words |
| Integer tree/leaf | 120,128 words | 120,027 words | 101 words |
| 4-character leaf/tree | 140,170 words | 140,023 words | 147 words |
| 4-character tree/leaf | 140,170 words | 140,023 words | 147 words |

### 5. Allocation-free membership completed

The lookup measurements allocate about two words per operation for both
implementations because the result is an option. Both `mem` implementations
now traverse directly, and `mem_get` proves agreement with `get`; mixed
present/absent benchmark passes allocate only fixed measurement overhead.

Build uses repeated persistent `set` over already sorted ranges. A proved
`of_sorted_array` or `of_sorted_list` builder could construct the Patricia
shape directly with less allocation. It should be reported separately from
incremental insertion because it answers a different API question. This is an
optional N5 item in `patricia-todo.md`.

### 6. Treat retained size as a representation tradeoff

Both Patricia variants retain eight words per binding versus six for
`Stdlib.Map`. The classic four-field branch layout is the same basic layout
presented by Okasaki and Gill in
[Fast Mergeable Integer Maps](<Okasaki and Gill - 1998 - Fast Mergeable Integer Maps.pdf>).
Reducing it requires a representation change, not a local expression rewrite:
for example, omit the integer prefix and route to a final leaf comparison, pack
the prefix/discriminator in a fixed-width backend, or remove the string sample
and accept representative descent. Each choice trades memory against lookup,
join, or merge work and requires new invariant proofs. Pursue it only if
retained memory dominates the target workload.

### 7. Proof-aligned one-descent `set` trial rejected for now

`StringPatricia.set_one_descent` is the source-level, one-pass counterpart of
the exception-based native `set` realizer. It has a well-formedness and lookup
refinement proof, and is now included in ordinary extraction and the randomized
structural oracle. A checked 10,000-binding wrapper trial temporarily selected
it in place of the realizer; functional checks passed, but allocation increased
materially because extracted `Set_complete`/`Set_bubble` values are allocated
along the routed path.

| Fixed-width 4-character strings | Exception realizer | Extracted worker |
| --- | ---: | ---: |
| Build allocation | 726,896 words | 993,458 words |
| Existing-key update allocation | 923,171 words | 1,578,027 words |

The trial also raised variable-length build allocation from 1,083,549 to
1,711,141 words and update allocation from 1,059,765 to 1,870,184 words.
The wrapper therefore continues to use the exception realizer. This is a
single-machine allocation comparison, not a formal cost result; the remaining
N2 task is to prove the exact realizer in a target-language logic or develop a
lower-allocation extracted source worker.

### 8. Native `union_left` retained; extracted workers are the proof oracle

The public integer and string wrappers use the handwritten native
`union_left` realizers. Their physical-identity checks preserve unchanged
branches. The extracted `union_left_specialized_changed_fuel_result` worker is
now proved equal to the established changed worker at its public bound, making
it the source-level functional oracle for a future refinement of the native
realizer, rather than the selected implementation.

The profile forces a major collection before and after each single operation,
keeps both input roots live during the final collection, checks every queried
binding and result cardinality, and reports allocation plus the extra retained
result graph.  These are 100,000-binding runs on the platform named above;
the string figures were the same for ordinary eight-byte keys and keys with a
192-byte common prefix.

| Workload | Integer native / proved / fuel | String native / proved / fuel | Retained result graph | Left root reused? |
| --- | ---: | ---: | ---: | --- |
| Disjoint | 379 / 438 / 463 | 100 / 165 / 186 | 50–87 words | No |
| Half overlap | 365 / 700,641 / 600,523 | 81 / 700,447 / 600,261 | 50–86 words | No |
| Subset | 176 / 700,524 / 600,310 | 26 / 700,361 / 600,202 | measurement baseline | Yes |
| Equal | 26 / 1,400,586 / 1,200,178 | 26 / 1,400,676 / 1,200,226 | measurement baseline | Yes |
| Empty right | 26 / 35 / 32 | 26 / 35 / 32 | measurement baseline | Yes |

“Measurement baseline” is the fixed GC-accounting noise (within five words)
when the result is the original root. The pattern matters more than the small
fixed disjoint numbers: both extracted workers physically retain only a
constant-size extra graph, but their recursive traversal allocates temporary
frames/closures linearly even when the final result is exactly the old left
tree. The fuel worker reduces this transient cost from about 14 to about 12
words per left binding, but remains orders of magnitude above the native
physical-sharing realization. Its `size` prepass has no observed linear
allocation cost. No timing or heap theorem is claimed.

## Further benchmark coverage

The benchmark is a useful checked comparison and smoke benchmark. Future
performance decisions would benefit from:

- a bulk-build workload if a bulk builder is added (the benchmark already
  includes generic leaf/tree `combine`, `elements`, and mixed hit/miss `mem`);
- physical-sharing counters or retained-node checks, so low allocation is
  attributed to reused nodes rather than inferred only from GC totals;
- pinned compiler configuration. These results used OCaml 4.14.3 without
  Flambda, so compiler changes must not be confused with data-structure changes.

The normal build already links a proof-aligned extraction beside the optimized
backend and differentially validates semantics. It is not timed by this
benchmark, so a future performance comparison could report both backends if
the extraction overhead itself becomes relevant.

These possible extensions are tracked under N6 in `patricia-todo.md`; this
measurement record is not a second task list.

The local paper motivates Patricia maps specifically by lookup, insertion, and
fast merge. The benchmark should keep those headline operations, while the
additional cases prevent the ordered-range union result from standing in for
all map workloads.

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

make -C patricia union-profile
PATRICIA_UNION_PROFILE_SIZE=100000 make -C patricia union-profile

PATRICIA_BENCH_SIZE=100000 make -C patricia benchmark
PATRICIA_BENCH_SIZE=1000000 PATRICIA_BENCH_STRING_LENGTHS=4,5 \\
  make -C patricia benchmark
```

`PATRICIA_BENCH_STRING_LENGTHS` selects a comma-separated non-empty list of
positive string lengths. Select longer keys when the requested size exceeds a
shorter base-62 key space; the default three-character workload can hold at
most 119,164 bindings per input map because the benchmark also constructs its
disjoint companion range.
