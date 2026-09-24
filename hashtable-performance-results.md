# Generated HAMT matched performance matrix

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
when major GC occurs during a sample, so the final report will show medians
and the raw ranges rather than claim that the policy makes timings identical.
