# Generated HAMT matched performance matrix

Latest complete five-way matrix: clean `bccd2a9` on 2026-09-24; see
[final matrix and decision](#final-five-way-matrix-at-bccd2a9) below. The
earlier sections preserve the original corrected baseline and isolated stages.

Date: 2026-09-23. Source revision: `bd0e69c6f6d8a701ce727412c8483ce14c291156` (clean).
The complete 228 JSONL records are archived in
[`benchmarks/hashtable-performance-matrix-bd0e69c.tar.xz`](benchmarks/hashtable-performance-matrix-bd0e69c.tar.xz).
Extract with `tar -xJf benchmarks/hashtable-performance-matrix-bd0e69c.tar.xz`.
The archive contains raw samples, per-operation median/min/max summaries,
machine and GC metadata, and representative post-GC live-heap measurements.
Its SHA-256 is `4cdd88917f6b61b9d9e2ef7deb24ff282f19ad8f74132a6b4de1b5e7e5c5b375`.

The isolated scalar-stage runs are archived in
[`benchmarks/hashtable-scalar-stage-a160354-3bb50a4.tar.xz`](benchmarks/hashtable-scalar-stage-a160354-3bb50a4.tar.xz)
(SHA-256 `15778257115977d7214b728eb27ebf9f50a361fdef6364641bd5d4b1e7001ab6`).

## Scope and validation

The matrix uses sizes 100, 2,000, 10,000 and 100,000; seeds 0, 31 and
104729; one warmup and seven measured repetitions per operation. Every HAMT
integer/string record has a matched Patricia record with the same inputs,
size, seed, repetition count and history policy. Ordinary integer inputs are
ascending, shuffled and root-slot collision; string inputs are fixed-width,
mixed-length and 192-byte common-prefix strings. Constant-hash and routing
divergence at depths 0–5 are measured at 100/2,000 only. The capped omission
at larger sizes avoids repeated quadratic collision histories.

`make hashtable-performance-matrix-validate` accepted all 228 clean paired
records. A separate record-level check found each expected implementation and
operation, every repetition index 0–6, matching median time/allocation, and
the expected retained-heap count: 9,918 operation summaries and 936 heap
measurements, with no missing groups. The 100/2,000 records include separate
latest-root and all-prefix post-GC heap passes. The 10,000/100,000 records
explicitly have no heap pass. The matrix was built and run on Linux aarch64,
64-bit OCaml 4.14.3; per-record OS/GC details are in the archive.

## Results

The table gives the median of **ratios of per-record medians** for the public
generated HAMT divided by the standalone array HAMT over all 72 ordinary
size/seed/distribution records. Ratios above 1 mean the generated backend
cost more. Each operation and distribution retains its individual measurements
in the archive; the aggregate does not include constant-hash or divergence
inputs.

| Operation | Time ratio | Allocation ratio |
| --- | ---: | ---: |
| `of_list` first-wins build | 1.53× | 3.56× |
| Repeated-set build | 1.39× | 2.50× |
| Lookup hit | 3.08× | 58.95× |
| Lookup miss | 1.50× | 15.63× |
| Membership hit | 2.99× | 58.95× |
| Membership miss | 1.45× | 15.63× |
| Existing set, latest root | 1.65× | 5.74× |
| New set, latest root | 1.69× | 6.19× |
| Present remove | 1.95× | 6.47× |
| Missing remove | 1.98× | 6.95× |
| Enumeration | 1.67× | 0.95× |

At 2,000 bindings and seed 31, ascending integers had public/standalone
`of_list` build medians of 0.512/0.276 ms and 5.340/1.394 MB allocated;
hit lookup was 0.300/0.114 ms and 3.749/0.127 MB. Fixed-width strings had
build medians of 0.593/0.349 ms and 5.146/1.280 MB; hit lookup was
0.548/0.144 ms and 9.509/0.126 MB. The corresponding Patricia build/hit
medians were 0.055/0.056 ms for integers and 0.141/0.126 ms for strings.
These are whole-operation runs over the input set, not per-key latencies.

The following matched 2,000-binding, seed-31 **time medians in milliseconds**
show all five implementations. The integer workload uses ascending positive
keys; the string workload uses fixed-width keys. Existing-key set uses the
latest-root policy for persistent maps and a prepared single-version table
for `Hashtbl`. Each cell is taken from the indicated implementation's
record; `Map` and `Hashtbl` are included in both paired processes, and the
table uses their HAMT-process samples.

| Integer operation | Generated HAMT | Handcoded HAMT | Patricia | AVL `Map` | Mutable `Hashtbl` |
| --- | ---: | ---: | ---: | ---: | ---: |
| Repeated-set build | 0.332 | 0.204 | 0.041 | 0.116 | 0.031 |
| Hit lookup | 0.300 | 0.114 | 0.056 | 0.099 | 0.032 |
| Existing-key set | 0.656 | 0.356 | 0.140 | 0.219 | 0.077 |
| Present removal | 0.464 | 0.248 | 0.051 | 0.081 | 0.051 |

| String operation | Generated HAMT | Handcoded HAMT | String Patricia | AVL `Map` | Mutable `Hashtbl` |
| --- | ---: | ---: | ---: | ---: | ---: |
| Repeated-set build | 0.400 | 0.258 | 0.098 | 0.175 | 0.042 |
| Hit lookup | 0.548 | 0.144 | 0.126 | 0.134 | 0.047 |
| Existing-key set | 0.934 | 0.437 | 0.366 | 0.308 | 0.107 |
| Present removal | 0.750 | 0.325 | 0.092 | 0.113 | 0.060 |

Over all 72 ordinary size/seed/distribution records, median generated/`Hashtbl`
time ratios are 10.63× for repeated-set build, 9.97× for hit lookup, 8.55×
for existing-key set and 10.66× for present removal. The corresponding
generated/handcoded ratios are 1.39×, 3.08×, 1.65× and 1.95×. Mutable
`Hashtbl` updates one table in place, while the other four maps preserve old
roots; these ratios describe measured workload cost, not equivalent storage
semantics. At this 2,000-binding point, integer hit lookup allocated 3.749 MB
in generated HAMT, 0.127 MB in handcoded HAMT and 0.032 MB in `Hashtbl`;
the string figures were 9.509, 0.126 and 0.032 MB. Reducing generated hit
lookup allocation is the clearest immediate path toward both comparisons.

The depth and collision records remain separate. At 2,000 bindings, seed 31,
the public/standalone build time ratio ranged from 1.72× to 2.80× over
divergence depths 0–5, while hit lookup ranged from 2.65× to 4.44×. The
constant-hash build/hit time ratios were 1.74×/2.02×. Collision allocation
is especially asymmetric for hit lookup, so it must not be averaged into the
ordinary result.

At 100/2,000 bindings, the public generated HAMT's measured live heap never
exceeded the standalone HAMT by 5% for either retained-root policy across
the 78 paired integer/string records. The largest public/standalone ratios
were 1.00027 for latest-root and 1.00002 for all-prefix roots. These are
post-GC observational measurements and do not prove a target heap theorem.

## Engineering decision

An isolated seven-repetition comparison on this machine used revisions
`a160354` immediately before native scalar routing and `3bb50a4` after
bounded scalar bitmap edits. `HashTableBenchmark.ml`,
`HashTableStringBenchmark.ml`, and their shared support files are identical
at those revisions. At 2,000 bindings and seed 31, the generated public
`of_list` integer build fell from 216.032 MB to 15.153 MB allocated (14.26×)
and from 7.390 ms to 1.109 ms. Fixed-width string build fell from 243.088 MB
to 19.596 MB (12.41×) and from 8.886 ms to 1.332 ms. This meets the
proposed 10× build-allocation target for the two historical distributions
**at the scalar stage under an identical harness**. The string harness at
these revisions has the older operation set, so its stage result should not
be treated as a direct comparison with the modern full matrix.
Integer hit lookup allocation fell from 109.788 MB to 3.749 MB (29.28×),
and fixed-width string hit lookup fell from 136.767 MB to 9.509 MB (14.38×).
The public workers still used source joins and collision fallbacks at this
stage; the comparison isolates the scalar-routing/bitmap-edit tranche from
the later direct-worker work, rather than each individual scalar primitive.

The final corrected matrix's corresponding build allocations are 5.340 MB
and 5.146 MB. The smaller values are encouraging, but its harness has since
changed; we do not assign that entire difference to one optimization stage.
The current matrix is the reproducible baseline for future work.

The proposed ordinary-operation 2× standalone median-time target is unmet:
hit lookup exceeded 2× in all 72 ordinary records, and other operations have
distribution-specific misses. The retained-heap 5% growth limit is met in
the measured representative sizes. The generated backend is materially better
than its historical allocation record but still has residual lookup and update
costs. The available primitive microbenchmark does not attribute those costs
inside whole-map operations; no storage specialization is selected without
that evidence. Correctness proofs, generated-shape audits, and finite target
tests remain separate from these runtime observations.

## Bounded comparison follow-up at `8026332`

The clean revision `8026332977692d103fe189107fdd23f6a19de9d9` realizes
bounded hash equality and slot order with guarded native integer comparisons.
Its 2,000-binding, seed-31, seven-repetition matrix covers all 13 planned
integer/string distributions at that size, including constant hash and all
six divergence depths. The validator accepted all 26 paired records. Raw
samples for all five implementations are in
[`benchmarks/hashtable-bounded-comparison-matrix-8026332.tar.xz`](benchmarks/hashtable-bounded-comparison-matrix-8026332.tar.xz)
(SHA-256 `ee61af7e501a22d2a3df7af00e5ca3751d0cb2caeedb699ad49b37867a39dfd3`).

Across the 13 distributions, the median generated hit-lookup allocation
ratio against `bd0e69c` is 0.15 and its median time ratio is 0.62. No
operation/allocation group regressed by more than 10%. Two missing-removal
time medians rose 12–15% while their allocation fell; those timing points
need repetition before they count as regressions. The constant-hash hit
allocation is essentially unchanged, as key comparisons within the long
collision bucket dominate that case.

At ascending integers, repeated-set build times (ms) for generated HAMT,
handcoded HAMT, Patricia, AVL and mutable `Hashtbl` were respectively
0.207/0.207/0.040/0.115/0.031; hit lookup was
0.182/0.113/0.056/0.098/0.032. At fixed-width strings the same order gave
0.264/0.262/0.090/0.168/0.045 for build and
0.211/0.145/0.132/0.142/0.048 for hit lookup. The generated/handcoded
build gap is small at these points, while lookup remains the clearer target.

## Direct-depth lookup follow-up at `dfb8680`

The clean revision `dfb86808ae1a7f65247d467094fcc6621b6fa452` routes
public lookup through six source-defined depth workers. Their source
equivalence to the fueled worker is proved. The same 2,000-binding, seed-31,
seven-repetition matrix accepted all 26 paired records. Raw samples are in
[`benchmarks/hashtable-direct-depth-matrix-dfb8680.tar.xz`](benchmarks/hashtable-direct-depth-matrix-dfb8680.tar.xz)
(SHA-256 `328474c86571bf23dd1ac2a5e4f400f8b56d06fb6f34fee31ff931cdaaca10f4`).
Across the 13 distributions, median generated lookup-hit time and allocation
ratios against `8026332` are 0.88 and 0.21. The generated/handcoded hit-time
ratio is 1.48 at this slice; their median allocation ratio is 1.00.

For ascending integers, generated/handcoded repeated-set build medians were
0.203/0.208 ms, lookup hit 0.164/0.113 ms, existing-key set
0.448/0.366 ms, and present removal 0.303/0.257 ms. For fixed-width strings
the corresponding medians were 0.263/0.261, 0.176/0.143, 0.495/0.426 and
0.358/0.317 ms. Generated hit lookup allocated exactly the same amount as the
handcoded HAMT in these two distributions: 127,376 and 125,712 bytes.

The collision cases remain separate. At 2,000 constant-hash integer keys,
generated/handcoded lookup allocated 160.112/0.112 MB and took
8.346/3.186 ms; present removal took 21.058/0.037 ms. At routing divergence
depth 5, lookup allocated 5.304/0.304 MB and took 0.591/0.239 ms. The
source bucket worker performs a checked indexed access at each collision
entry; its target option and recursive-call costs remain visible. These
figures are a reason to retain collision inputs in the final matrix and not
to infer parity from the ordinary lookup result.

## Bounded collision scans at `952fe24`

The clean revision `952fe24` binds the three proved first-match bucket
workers to bounded scans in the private array adapter. The target contract
states their list-view behavior; target tests cover duplicate keys, custom
equivalences, off-end indices and budgets, and fresh changed updates. The
extraction audit requires these exact bindings. The 2,000-binding, seed-31,
seven-repetition matrix validated all 26 paired records. Raw samples are in
[`benchmarks/hashtable-bucket-scan-matrix-952fe24.tar.xz`](benchmarks/hashtable-bucket-scan-matrix-952fe24.tar.xz)
(SHA-256 `c3138bf1337afaed96c5cc7800460452298f594955c10d115271b95fb5be1cf9`).

For 2,000 constant-hash integer keys, generated lookup hit fell from
8.346 to 3.871 ms and from 160.112 MB to 0.112 MB allocated; the handcoded
HAMT measured 3.178 ms and the same 0.112 MB allocation. First-wins build
fell from 42.170 to 28.982 ms and from 464.568 to 16.504 MB allocated.
At routing divergence depth 5, generated lookup hit fell from 0.591 to
0.440 ms and from 5.304 to 0.304 MB allocated; handcoded lookup allocated
the same 0.304 MB. Across the 13 distributions, the median new/old time
ratio is 1.01 for ordinary build and hit lookup; the median allocation ratio
is 1.00 because unchanged ordinary paths do not call the bucket adapter.

Constant-hash present removal still took 19.337 ms in generated HAMT versus
0.037 ms in the handcoded HAMT. The generated bucket is a persistent array:
removing every key copies each shrinking array. The handcoded bucket is a
list, and this workload removes keys in list-head order. Closing that
particular gap requires a different collision representation and fresh
source/target proof; it cannot follow from a faster scan alone.

Two >10% time rises in the clean slice were repeated with standalone
seven-repetition runs from detached clean checkouts. At depth 4, generated
present removal was 0.565 ms before and 0.775 ms after the adapter binding
(3.300/3.230 MB allocated); this is a measured local regression amid larger
lookup and collision-build gains. A target-only tail-recursive scan
experiment was slower and discarded. A short-bucket removal path screened at
0.673 ms while keeping the constant-hash results; the final matrix includes
that path. Root-slot new-set reversed its apparent rise in the clean rerun,
0.617/0.585 ms, with identical allocation and no bucket scan on that
workload. The four raw rerun records are in
[`benchmarks/hashtable-bucket-regression-reruns-dfb8680-952fe24.tar.xz`](benchmarks/hashtable-bucket-regression-reruns-dfb8680-952fe24.tar.xz)
(SHA-256 `8f84be1ae5219565077ca8257e54428b1a1f4624f8e31da8941b35aea330330f`).

## Matrix runtime policy

The original full matrix used `Gc.compact` before every timed sample. A
100,000-binding ascending-integer, seven-repetition diagnostic took about
102 seconds with `Gc.full_major` and 19 seconds with `Gc.minor`; at 10,000,
the corresponding compact/major/minor times were 12.0/6.3/0.9 seconds.
The matrix runner now uses compaction for 100/2,000-binding records and a
minor collection for 10,000/100,000-binding records. A metadata field records
the selected policy, and the validator checks it. The historical archives
lack that field and mean `compact`; validate those with
`HASHTABLE_MATRIX_GC_POLICY_HIGH=compact`. Large-size timed samples can vary
when major GC occurs during a sample. The final results report medians and
retain the raw ranges rather than assuming identical timing conditions.

## Final five-way matrix at `bccd2a9`

Revision `bccd2a95d91454f08d76f046a5dabf39f6096687` passed `make all`
in a detached clean checkout and the four-size matrix runner. The raw data
are in
[`benchmarks/hashtable-performance-matrix-bccd2a9.tar.xz`](benchmarks/hashtable-performance-matrix-bccd2a9.tar.xz)
(SHA-256 `b9e6137ef3b7a4ad7a0a9c5e7a4ddfc100e162a3c5d3e96eb989365ef544e987`).
The validator accepted 228 clean paired HAMT/Patricia records. An independent
audit found 9,918 operation summaries, 69,426 samples with every repetition
index 0–6, and 936 retained-heap records. Sizes, seeds, distributions and
operation boundaries match the original matrix. The run took about 18 minutes
8 seconds from log creation to the final validator message on this host.

The 100 and 2,000-binding records use pre-sample compaction and measure
post-GC retained heap. The 10,000 and 100,000-binding records use a minor
collection before each timed sample and omit the expensive retained-heap
pass. Every record states its policy. Ratios below compare implementations
within the same record. At 100,000 bindings, the generated HAMT's median
sample max/min ranges across ordinary records were 2.17 for repeated-set
build, 1.38 for hit lookup, 1.89 for existing set and 1.62 for present
removal; interpret individual large-size timings with those ranges in view.

### Ordinary operations across all five implementations

The following entries are medians of per-record median-time ratios over the
72 ordinary records: six integer/string distributions × four sizes × three
seeds. Each ratio is **generated HAMT / named implementation**; values above
one mean the generated HAMT took longer. The Patricia value comes from the
paired process, while the other three competitors share the HAMT process.

| Operation | Handcoded HAMT | Mutable `Hashtbl` | Patricia | AVL `Map` |
| --- | ---: | ---: | ---: | ---: |
| Repeated-set build | 1.10× | 7.53× | 2.75× | 1.77× |
| Hit lookup | 1.44× | 4.80× | 2.75× | 1.84× |
| Existing-key set, latest root | 1.25× | 5.82× | 2.56× | 2.06× |
| Present removal | 1.19× | 6.66× | 4.96× | 3.87× |

For each ordinary distribution, the next table gives generated/handcoded
median **time / allocation** ratios over its 12 size/seed records. The
separate mutable table gives generated/`Hashtbl` median **time** ratios for
the same operations. Constant-hash and divergence inputs remain separate.

| Distribution | Build time / allocation | Hit time / allocation | Existing set time / allocation | Present removal time / allocation |
| --- | ---: | ---: | ---: | ---: |
| Integer ascending | 1.16 / 1.49 | 1.45 / 1.00 | 1.28 / 1.47 | 1.21 / 1.56 |
| Integer shuffled | 1.13 / 1.50 | 1.46 / 1.00 | 1.26 / 1.47 | 1.17 / 1.57 |
| Integer root-slot collision | 1.26 / 1.62 | 1.65 / 1.00 | 1.47 / 1.57 | 1.37 / 1.68 |
| String fixed-width | 1.04 / 1.53 | 1.35 / 1.00 | 1.16 / 1.48 | 1.17 / 1.60 |
| String mixed-length | 1.03 / 1.53 | 1.20 / 1.00 | 1.22 / 1.49 | 1.12 / 1.60 |
| String common-prefix | 1.00 / 1.53 | 1.07 / 1.00 | 1.06 / 1.49 | 1.04 / 1.60 |

| Distribution | Build vs mutable | Hit vs mutable | Existing set vs mutable | Present removal vs mutable |
| --- | ---: | ---: | ---: | ---: |
| Integer ascending | 8.99× | 5.32× | 6.46× | 6.62× |
| Integer shuffled | 10.17× | 4.92× | 6.39× | 7.66× |
| Integer root-slot collision | 12.50× | 6.72× | 8.48× | 9.16× |
| String fixed-width | 6.86× | 4.10× | 5.38× | 6.18× |
| String mixed-length | 5.25× | 4.10× | 4.76× | 5.97× |
| String common-prefix | 2.50× | 1.93× | 2.40× | 2.36× |

Hit and miss lookup and membership allocated exactly the same bytes in the
generated and handcoded HAMTs in all 72 ordinary records. Build and update
still allocate roughly 1.5–1.6× as much in the generated backend. Mutable
`Hashtbl` updates a single table; the persistent maps produce new roots, so
their update/allocation ratios describe different storage semantics. At
2,000 bindings, seed 31, ascending integer generated/handcoded/Patricia/AVL/
mutable hit times were 0.164/0.116/0.069/0.102/0.033 ms; fixed-width string
hit times were 0.175/0.141/0.131/0.138/0.046 ms. Their generated/handcoded
hit allocations were 127,376/127,376 and 125,712/125,712 bytes, respectively.

### Progress against the original compact-policy baseline

The following comparison uses only the 36 ordinary 100/2,000-binding records,
where both `bd0e69c` and `bccd2a9` used compaction and the same workload
boundaries. New/old columns are medians of each record's generated-HAMT
ratio; gap columns are medians of generated/competitor ratios at each stage.

| Operation | Generated time new/old | Generated allocation new/old | Handcoded time gap old → new | Mutable time gap old → new |
| --- | ---: | ---: | ---: | ---: |
| Repeated-set build | 0.76 | 0.55 | 1.52× → 1.06× | 8.08× → 6.32× |
| Hit lookup | 0.47 | 0.015 | 3.25× → 1.47× | 8.91× → 3.83× |
| Existing-key set | 0.66 | 0.20 | 1.95× → 1.25× | 5.77× → 4.13× |
| Present removal | 0.61 | 0.17 | 2.00× → 1.18× | 7.72× → 4.72× |

The ordinary twofold handcoded time bound now holds for 69/72 hit-lookup
records, 71/72 repeated-set builds, and all 72 existing-key set and present
removal records. It is still not universal: the largest ordinary hit ratio
was 2.24×. The mutable gap narrowed substantially but remains 3.83× for
hit lookup and 4.72–6.32× for the other three operations in the comparable
compact-policy subset. No parity with mutable `Hashtbl` is claimed.

### Capped collisions and retained heap

At the 2,000-binding cap, the next table gives median generated/handcoded
**time / allocation** ratios over three seeds for each integer collision
distribution. The 100-binding cap is also measured in the raw archive; its
individual times are short enough to be more sensitive to timer noise.

| Distribution | Build time / allocation | Hit time / allocation | Existing set time / allocation | Present removal time / allocation |
| --- | ---: | ---: | ---: | ---: |
| Constant hash | 1.34 / 0.17 | 1.17 / 1.00 | 1.52 / 0.34 | 525.31 / 93.25 |
| Divergence depth 0 | 0.85 / 1.48 | 1.43 / 1.00 | 1.22 / 1.48 | 1.21 / 1.60 |
| Divergence depth 1 | 1.31 / 1.61 | 1.71 / 1.00 | 1.38 / 1.59 | 1.38 / 1.73 |
| Divergence depth 2 | 1.40 / 1.73 | 1.98 / 1.00 | 1.59 / 1.68 | 1.50 / 1.84 |
| Divergence depth 3 | 1.41 / 1.84 | 2.00 / 1.00 | 1.87 / 1.76 | 1.60 / 1.94 |
| Divergence depth 4 | 1.75 / 1.93 | 2.28 / 1.00 | 1.73 / 1.74 | 2.12 / 1.95 |
| Divergence depth 5 | 0.81 / 0.83 | 1.75 / 1.00 | 1.02 / 0.95 | 2.36 / 2.63 |

At 2,000 constant-hash keys, over three seeds, the median generated/handcoded
hit-time ratio was 1.17× with equal allocation. Repeated-set build was 1.34×
as slow but allocated only 0.17× as much. Present removal remained 525× as
slow and allocated 93× as much because it repeatedly copies a shrinking
persistent array while the handcoded list bucket removes the head. At
divergence depth 5, hit lookup was 1.75× as slow with equal allocation;
present removal was 2.36× as slow and allocated 2.63× as much. All 42 capped
integer records and their Patricia companions remain in the archive, with
latest-root and all-prefix history policies measured separately.

Across all 78 paired HAMT records with a heap pass, the largest generated/
handcoded retained-heap ratios were 1.000266 for the latest root and 1.000027
for all-prefix roots, below the planned 5% growth limit. Constant-hash
generated retained heap was smaller than handcoded retained heap because the
two collision representations differ. These post-GC measurements are finite
target observations, while source correctness, array-view contracts and
foreign OCaml realization remain separate obligations.

| Distribution, 100/2,000 bindings | Largest latest-root ratio | Largest all-prefix ratio |
| --- | ---: | ---: |
| Integer ascending | 1.000000 | 1.000000 |
| Integer shuffled | 1.000000 | 1.000013 |
| Integer root-slot collision | 1.000000 | 1.000018 |
| Integer constant hash | 0.668885 | 0.203552 |
| Integer divergence depths 0–5 | 1.000266 | 1.000023 |
| String fixed-width | 1.000149 | 1.000027 |
| String mixed-length | 1.000150 | 1.000027 |
| String common-prefix | 1.000000 | 1.000000 |
