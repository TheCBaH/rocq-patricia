# Patricia benchmark results

- Run date: 2026-08-29
- Last reviewed: 2026-09-09 (dated native-verification profile added below)
- Command: `make -C patricia benchmark`
- Platform: aarch64 Linux 7.0.0-28-generic; OCaml 4.14.3 native code
- Compiler configuration: `architecture: arm64`, `model: default`,
  `word_size: 64`, `system: linux`, `flambda: false`, `safe_string: true`,
  `native_c_compiler: gcc -O2 -fno-strict-aliasing -fwrapv -pthread -fPIC
  -D_FILE_OFFSET_BITS=64`

This document is the measurement record and reproduction guide. Performance
analysis is in [`patricia-str.md`](patricia-str.md). Project-wide work is tracked
in [`patricia-todo.md`](patricia-todo.md); detailed native-verification work has
its separate tracker in
[`patricia-native-verification.md`](patricia-native-verification.md).

### Native string primitive baseline (2026-09-11)

`make string-primitive-profile` is the reproducible primitive-level baseline
for the then-handwritten `StringBits` extraction bodies. It creates strings
before timed/allocation regions, consumes every result, takes seven samples
after one warm-up, and checks short binary inputs and long workload endpoints
against the proof-aligned extracted oracle. It is not an executable-candidate
comparison and does not establish target primitive correctness.

On the compiler configuration recorded above, the 1,024-byte workload gave
these medians (allocated words are per whole batch):

| Primitive workload | Repetitions | Median | Range | Words |
| --- | ---: | ---: | ---: | ---: |
| `bit_at`, cycling positions | 200,000 | 3.015 ns/op | 2.971–3.105 | 24 |
| `first_diff`, same object | 100,000 | 1.321 ns/op | 1.321–1.400 | 24 |
| `first_diff`, equal copies | 20,000 | 632.393 ns/op | 631.344–639.808 | 160,024 |
| `first_diff`, late difference | 20,000 | 636.351 ns/op | 635.493–645.304 | 300,048 |
| bounded scan, late split | 20,000 | 1,149.094 ns/op | 1,094.353–1,161.051 | 24 |
| bounded scan, proper prefix | 20,000 | 1,150.703 ns/op | 1,147.640–1,160.753 | 24 |

The 24-word batches are measurement overhead. The two non-identity
`first_diff` workloads include the fixed `Some` result allocation; no
allocation proportional to the scanned prefix appears in this baseline.

The source-defined packed `bit_at` worker was then measured by the same command
at **3.185 ns/op** (3.135–3.340) with the same 24-word batch overhead. At that
point it remained a candidate; the 2026-09-12 section records its later
selection after the map-level acceptance gate.

The unselected source-defined bounded-prefix candidate was checked against the
current primitive on the harness’s valid packed-position matrix. On the long
workloads it measured 857.556 ns/op (830.555–900.495) for a late difference
and 854.802 ns/op (826.347–862.193) for a proper prefix, compared with
1,134.300 and 1,129.007 ns/op for the current body. Both versions reported
only the 24-word batch measurement overhead. These primitive results are not
the required 10K/100K map acceptance comparison.

### Repeated string-map baseline (2026-09-11)

Three native `make benchmark` runs at 10,000 and 100,000 bindings used
four-byte keys, variable keys up to four bytes, five union samples, and the
compiler configuration recorded above. Every run ended with `Patricia
comparison benchmark: ok`. This is the baseline variability record for later
candidate comparisons; inputs and all map results are checked by the benchmark
before reporting timings.

| Size | Build ms | Lookup ns/op | Membership ns/op | Overlap union us | Subset union us | Equal union us |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10K (min–max) | 0.809–0.843 | 68.7–74.7 | 64.5–66.5 | 67.219–69.462 | 64.097–64.559 | 127.718–132.345 |
| 100K (min–max) | 9.610–9.849 | 73.3–74.8 | 66.3–67.8 | 638.008–653.029 | 611.067–681.877 | 1,180.887–1,270.056 |

Retained/build-allocation words were invariant across the three samples:
79,993/638,258 at 10K and 799,991/7,391,327 at 100K. Disjoint/overlap/subset/
equal union allocations were 106/96/3/1 words at 10K and 145/140/32/30 at
100K. Disjoint-union elapsed time is below reliable resolution (0.186–0.253
us at 10K and 0.954–3.099 us at 100K), so allocation is the dependable signal
for that case.

### Selected source-defined string workers (2026-09-12)

The selected `StringBits.bit_at`, `first_diff`, and
`agrees_before_bounded` bindings now respectively target
`NativeStringWorker.packed_bit_at`,
`NativeStringWorker.first_diff_indexed_with_identity`, and
`NativeStringWorker.bounded_prefix_packed`. The historical OCaml bodies are
retained only in isolated benchmark fixtures.

`make string-primitive-profile` used seven paired, alternating samples after
warm-up, with inputs created outside measurement. It checked selected and
generated workers against the frozen historical body and the proof-aligned
reference extraction. On 1,024-byte inputs, selected `first_diff` improved
equal copies from 622.749 to 596.845 ns/op and late difference from 626.445
to 606.406 ns/op, while batch words fell from 160,024/300,048 to 24/40,024.
Bounded late/proper-prefix scans improved from 1,111.543/1,097.953 to
854.349/849.307 ns/op with the same 24-word measurement overhead. Packed
`bit_at` was 3.455 versus 3.515 ns/op; its seven-sample ranges overlap. The
identity, empty, proper-prefix, early-difference, every terminal tag, binary,
separately allocated equality, exhaustive one-byte and oracle checks passed.

`PATRICIA_STRING_ROUNDS=5 PATRICIA_BENCH_SHORT_BATCH=8
make string-worker-performance` built five independently linked variants
(historical, each isolated worker, and all selected workers) and interleaved
them at 10K and 100K. Each run exercised fixed four-byte, variable up-to-four
byte, and 192-byte-common-prefix keys; build/random build, lookup,
membership, update, unchanged update, removal, combine, mixed operations,
and left/right disjoint/overlap/subset/equal/separately-built-equal unions.
Every completed run reported `Patricia comparison benchmark: ok`. The summary
requires five samples per row; the all-workers variant had no timing range
wholly above its historical baseline and no median allocation increase. Its
fixed-four-byte 100K build/lookup/membership medians were 10.105 ms/74.4/66.2
ns/op versus 9.973 ms/75.4/69.3 ns/op, with 6,082,676 versus 7,391,327 build
words. Its variable-key 100K build/lookup/membership medians were 17.564
ms/75.2/56.2 ns/op versus 17.526 ms/78.1/55.6 ns/op, with 10,283,200 versus
11,578,414 build words. Timing dispersion is retained in the generated CSV,
not collapsed into a portability claim.

The acceptance fixture and summarizer are in
[`benchmarks/`](benchmarks/README.md); its temporary artifact directory holds
the exact compiler configuration, source hashes, workload settings, binaries
and raw logs. The measurements establish this toolchain/machine acceptance
gate only. They do not prove primitive execution, extraction/compiler
correctness, or a universal performance/GC property.

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

The CI workflow pins OCaml 4.14.3. Run `make compiler-config` with every
comparable native benchmark series to record the target-dependent compiler
configuration; the command reports the OCaml version, target, word size,
Flambda setting, safe-string mode, and native C compiler flags.

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
level of a successful deletion. The 2026-09-01 reevaluation at 10,000 bindings
allocated 452,104 words for integer Patricia and 588,296 for fixed
four-character strings, compared with 433,422 for `Stdlib.Map` in both cases.
The previous lower Patricia figures (308,608 and 441,976) predate that proved
change signal. A native physical-child-identity replacement could reduce this
transient cost, but would widen the trusted extraction boundary with the same
heap/compiler contract as handwritten union sharing. The current implementation
therefore retains the proved option signal.

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

### Proof-aligned extraction profile

`make reference-profile` compiles a native executable containing only the
ordinary extraction of the Rocq definitions. It measures 1,000 positive keys
and 1,000 fixed eight-byte string keys by default, checking every build,
update, and union result against `Stdlib.Map`. Its modules intentionally remain
separate from the optimized backend because both extraction sets define support
modules such as `Nat`; run it beside—not inside—the regular benchmark.

On the recorded compiler configuration, the following 1,000-binding run used
the same consecutive integers and eight-character hexadecimal strings as the
matching optimized workload. Lookup is three complete successful passes. The
optimized union rows are batched medians while the reference profile uses one
operation, so the figures are diagnostic evidence of extraction overhead, not
precision performance comparisons.

| Workload | Optimized time / allocation | Proof-aligned time / allocation |
| --- | ---: | ---: |
| Integer build | 0.051 ms / 33,677 | 0.870 ms / 1,860,582 |
| Integer lookup (3 passes) | 0.077 ms / 6,047 | 3.240 ms / 10,240,600 |
| Integer update | 0.039 ms / 52,965 | 1.185 ms / 3,472,608 |
| Integer disjoint union | 0.000 ms / 139 | 0.021 ms / 24,944 |
| Integer half-overlap union | 0.002 ms / 125 | 0.116 ms / 316,776 |
| String build (8 bytes) | 0.055 ms / 56,098 | 11.354 ms / 19,763,028 |
| String lookup (3 passes) | 0.146 ms / 6,047 | 3.243 ms / 5,484,615 |
| String update | 0.061 ms / 65,700 | 2.496 ms / 3,718,185 |
| String disjoint union | 0.000 ms / 60 | 0.095 ms / 163,923 |
| String half-overlap union | 0.008 ms / 36 | 4.786 ms / 8,307,071 |

Reproduce the profile with `PATRICIA_REFERENCE_PROFILE_SIZE=1000 make
reference-profile`; use `PATRICIA_BENCH_SIZE=1000
PATRICIA_BENCH_STRING_LENGTHS=8 PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH=8
make benchmark` for the matching optimized workload. The ordinary extraction
is retained for semantic differential testing, not as the selected runtime
implementation.

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

### 4. Equality-aware unchanged update evaluated

The benchmark now contains a local candidate for an equality-aware update: it
performs `get key map` first, returns the original map when a supplied equality
test accepts the existing value, and otherwise calls `set`. It is not exported
by either supported wrapper: doing so would add an equality-reflection contract
and a new proof-facing operation to the frozen custom API.

The candidate was checked to return the exact original root after updating
every existing binding with its current value. At 10,000 bindings, it allocated
20,030 words for both integer and fixed four-character string maps, versus
769,162 and 923,179 words respectively for the ordinary existing-key update.
The remaining allocation is the `Some` result of each lookup; no tree path is
rebuilt. It also measured 0.372 ms for integer maps and 0.551 ms for the fixed
string maps, compared with 0.807 ms and 1.142 ms for ordinary updates in that
run. This justifies a future API/proof extension if the operation becomes
useful, but does not itself change the supported API.

### 5. Generic-combine leaf cases completed

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

### 6. Allocation-free membership completed

The lookup measurements allocate about two words per operation for both
implementations because the result is an option. Both `mem` implementations
now traverse directly, and `mem_get` proves agreement with `get`; mixed
present/absent benchmark passes allocate only fixed measurement overhead.

Build uses repeated persistent `set` over already sorted ranges. The supported
wrappers also expose proved generic `of_list` batch loading (with a documented
first-binding-wins duplicate policy); its current source definition is exactly
that `set` recurrence, so it is not measured as a separate performance result.
A future direct `of_sorted_array` or `of_sorted_list` builder could construct
the Patricia shape with less allocation and should be reported separately from
incremental insertion because it answers a different API question.

### 6. Treat retained size as a representation tradeoff

Both Patricia variants retain eight words per binding versus six for
`Stdlib.Map`. The classic four-field branch layout is the same basic layout
presented by Okasaki and Gill in
[Fast Mergeable Integer Maps](papers/okasaki-gill-1998-fast-mergeable-integer-maps.pdf),
whose archived author-path origin is documented in
[`papers/README.md`](papers/README.md#okasaki-and-gill--fast-mergeable-integer-maps).
Reducing it requires a representation change, not a local expression rewrite:
for example, omit the integer prefix and route to a final leaf comparison, pack
the prefix/discriminator in a fixed-width backend, or remove the string sample
and accept representative descent. Each choice trades memory against lookup,
join, or merge work and requires new invariant proofs. Pursue it only if
retained memory dominates the target workload.

### 7. Source-extracted string `set` replaces the exception realizer

The one-descent source worker remains useful as a proof and control-flow model,
but ordinary extraction allocates a `Set_complete`/`Set_bubble` result at each
routed branch. Threading its fresh leaf removes one avoidable allocation, but
not the result wrappers. The original two-descent source definition avoids
those wrappers entirely. It is now the public extracted `StringPatricia.set`;
the handwritten exception realizer has been removed.

`make set-profile` checks all outputs and reports allocation independently of
the supported-wrapper benchmark. On the checked 10,000-binding fixed-width
workload:

| Worker | Build allocation | Existing-key update allocation |
| --- | ---: | ---: |
| Former exception realizer | 667,306 words | 911,607 words |
| Ordinary one descent | 881,851 words | 1,553,493 words |
| Shared-leaf one descent | 687,362 words | 1,133,381 words |
| Public source two descent | 540,777 words | 819,662 words |

This is machine-specific allocation evidence, not a formal cost theorem. The
ordinary extracted public worker still relies on the usual extraction/compiler
boundary and the separately audited native string primitives, but no longer on
OCaml exception control flow.

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

### Native verification investigation (2026-09-09)

Rebuilt extraction and the native profile with
`PATRICIA_UNION_PROFILE_SIZE=10000 make union-profile` from this directory.
The run used Rocq 9.2, OCaml 4.14.3, arm64/Linux, 64-bit,
`flambda: false`, `safe_string: true`, and completed with
`Patricia union-worker allocation profile: ok`.

| 10K workload | Public handwritten | Generated native-shaped | Native fuel | Inlined native fuel |
| --- | ---: | ---: | ---: | ---: |
| Integer half overlap | 243 | 80,287 | 120,351 | 110,342 |
| Eight-byte string half overlap | 86 | 80,126 | 120,230 | 110,218 |
| Integer equal inputs | 26 | 160,016 | 240,014 | 220,015 |
| String equal inputs | 26 | 160,016 | 240,014 | 220,015 |

All numbers are allocated words. Equal-input rows pass the same input root
twice, not independently constructed equal maps. The profiled workers retained
the same input-node sharing in these cases. Adding a 192-byte common prefix
gave the same string allocation figures. This supports the existing diagnosis
of temporary allocation despite retained sharing; it is not an elapsed-time
comparison or a universal constant-allocation result.

Generated nested recursion returns capturing functions; the fuel worker still
passes capturing callbacks through the native-`nat` eliminator. The fuel
wrapper also computes input sizes, regardless of the allocation cost of that
prepass. Removing the runtime measure entirely by recursion on an erased
accessibility proof is therefore a distinct, unmeasured experiment, as is a
genuine Flambda build. See the separate native-verification tracker and
[Leroy's paper](papers/leroy-well-founded-recursion.pdf).

## Further benchmark coverage

The benchmark is a useful checked comparison and smoke benchmark. It now
includes physical subtree-sharing counters in `make union-profile`: every
result is traversed and the report gives its node count plus nodes physically
reachable from either input. This is diagnostic evidence only, not a sharing
or allocation guarantee. Future performance decisions would still benefit
from:

- a bulk-build workload if a bulk builder is added (the benchmark already
  includes generic leaf/tree `combine`, `elements`, and mixed hit/miss `mem`);
- timing the proof-aligned backend when extraction overhead itself becomes a
  performance question.

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
