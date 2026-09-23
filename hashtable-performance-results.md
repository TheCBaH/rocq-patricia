# Generated HAMT matched performance matrix

Date: 2026-09-23. Source revision: `bd0e69c6f6d8a701ce727412c8483ce14c291156` (clean).
The complete 228 JSONL records are archived in
[`benchmarks/hashtable-performance-matrix-bd0e69c.tar.xz`](benchmarks/hashtable-performance-matrix-bd0e69c.tar.xz).
Extract with `tar -xJf benchmarks/hashtable-performance-matrix-bd0e69c.tar.xz`.
The archive contains raw samples, per-operation median/min/max summaries,
machine and GC metadata, and representative post-GC live-heap measurements.
Its SHA-256 is `4cdd88917f6b61b9d9e2ef7deb24ff282f19ad8f74132a6b4de1b5e7e5c5b375`.

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

The historical pre-optimization 2,000-binding build allocations were
215.905 MB for integers and 243.088 MB for strings. The current corresponding
measurements are 5.340 MB and 5.146 MB, respectively. The apparent reductions
are about 40× and 47×, but the historical harness predates the corrected
operation boundaries and seven-repetition protocol. Thus the proposed 10×
**paired corrected-baseline** target cannot be claimed from these two runs.
The corrected current matrix is the reproducible baseline for future work.

The proposed ordinary-operation 2× standalone median-time target is unmet:
hit lookup exceeded 2× in all 72 ordinary records, and other operations have
distribution-specific misses. The retained-heap 5% growth limit is met in
the measured representative sizes. The generated backend is materially better
than its historical allocation record but still has residual lookup and update
costs. The available primitive microbenchmark does not attribute those costs
inside whole-map operations; no storage specialization is selected without
that evidence. Correctness proofs, generated-shape audits, and finite target
tests remain separate from these runtime observations.
