# Patricia benchmark results

## Current implementation: specialized native merge and biased union

The measurements below record the baseline that motivated the change.  The
current extracted OCaml backends no longer use that slow path for normal
native execution:

- `Patricia.combine` and `StringPatricia.combine` recurse directly, so they
  do not first traverse both maps to calculate proof-side fuel.
- `union_left` is specialized in both backends.  It reuses one-sided
  subtrees, joins disjoint prefixes immediately, and only rebuilds a path
  whose bindings actually change.  `union_right` is its argument-reversed
  counterpart.

The Rocq definitions and their fuel proofs remain the executable
specification.  The direct recursive extraction is an optimized native
refinement, in the same trusted boundary as the existing native bit and
string primitives.

Post-change validation on the same platform passed both
`make -C patricia test` and the benchmark's `Stdlib.Map` equivalence checks.
The short operations are timer-resolution limited, but allocation makes the
structural behavior clear:

| Input size / keys | Integer disjoint P / AVL (ms) | Integer disjoint allocation P / AVL | Integer 50% overlap P / AVL (ms) | Integer overlap allocation P / AVL |
| --- | ---: | ---: | ---: | ---: |
| 10,000 | 0.001 / 0.004 | 288 / 2,404 | 0.017 / 0.070 | 243 / 81,324 |
| 100,000 | 0.003 / 0.008 | 379 / 3,620 | 0.236 / 2.021 | 365 / 965,872 |

At 100,000 bindings, the direct string implementation likewise used
406 words for a disjoint union and 400,347 words for a 50%-overlapping
union, versus 3,620 and 965,872 words respectively for AVL (across the
three tested key lengths).  Thus the former whole-tree rebuild diagnosis is
now a historical baseline rather than a property of `union_left`.

## Baseline measurements (before specialized biased union)

Run date: 2026-08-29  
Command: `PATRICIA_BENCH_SIZE=10000 make -C patricia benchmark`  
Platform: aarch64 Linux 7.0.0-28-generic; OCaml 4.14.3 native code.

The benchmark compares the extracted Patricia implementations with
`Stdlib.Map` (its balanced AVL tree).  Each input tree contains 10,000 unique
bindings.  It validates every measured result against `Stdlib.Map`; the run
ended with `Patricia comparison benchmark: ok`.

## Baseline summary

| Workload | Integer Patricia vs. AVL | String Patricia vs. AVL |
| --- | --- | --- |
| Retained map size | 8 vs. 6 words/binding | 8 vs. 6 words/binding |
| Lookup | 1.9x faster | 1.1x--1.2x faster |
| Insert fresh keys | 4.9x faster | 1.2x--1.8x slower |
| Update existing keys | 1.7x faster | 1.2x--1.5x slower |
| Remove keys | 3.7x faster | approximately equal |
| Disjoint left-biased union | 48x slower; 83x more allocation | 150x--200x slower; 179x more allocation |
| 50%-overlapping left-biased union | 5.9x slower; 4.7x more allocation | 6.1x--7.8x slower; 5.2x--5.3x more allocation |

The central result is negative but actionable: union does not have the fast
disjoint-tree behavior expected of a specialized mergeable Patricia map.
For example, the integer disjoint union took 0.184 ms and allocated 200,364
words, compared with 0.004 ms and 2,404 words for AVL.  The string cases show
the same pattern (0.754--0.779 ms and 429,098 words, versus 0.004--0.005 ms
and 2,404 words for AVL).

This supports the review finding in `patricia.md`: public `combine` first
computes `size left + size right` as runtime fuel, then its one-sided mapping
functions rebuild retained subtrees.  `union_left` is currently expressed via
that generic path, so even immediately disjoint input trees are traversed and
rebuilt rather than joined while reusing their existing nodes.  The benchmark
is evidence for this implementation diagnosis, not a proof of its asymptotic
cost.

## Measurements

Times for per-key operations are nanoseconds per operation.  Union times and
allocation are for one union of two 10,000-binding inputs.  Allocation is in
OCaml heap words.

### Integer keys

| Operation | Patricia | Stdlib.Map | Patricia allocation | AVL allocation |
| --- | ---: | ---: | ---: | ---: |
| Build | 0.822 ms | 1.624 ms | 465,632 | 973,858 |
| Lookup | 44.7 ns/op | 85.5 ns/op | 60,043 | 60,043 |
| Add fresh | 46.2 ns/op | 225.4 ns/op | 507,582 | 1,087,954 |
| Update | 82.4 ns/op | 143.5 ns/op | 769,164 | 785,116 |
| Remove | 23.9 ns/op | 87.4 ns/op | 308,608 | 433,420 |
| Disjoint union | 0.184 ms | 0.004 ms | 200,364 | 2,404 |
| 50% overlap union | 0.465 ms | 0.079 ms | 385,769 | 81,324 |

Construction allocates about 52% fewer words for integer Patricia than AVL,
but its retained representation is one-third larger (8 rather than 6
words/binding).  Lookup, insertion, update, and removal all favor the integer
Patricia tree on this workload.  Union is the exception by a wide margin.

### String keys

| Key length | Build P / AVL (ms) | Lookup P / AVL (ns/op) | Add P / AVL (ns/op) | Update P / AVL (ns/op) | Remove P / AVL (ns/op) |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3 | 1.997 / 1.991 | 78.6 / 95.1 | 232.8 / 187.7 | 199.7 / 152.2 | 78.8 / 81.4 |
| 4 | 2.520 / 1.680 | 81.4 / 89.2 | 297.1 / 167.5 | 188.2 / 140.2 | 77.0 / 76.6 |
| 5 | 2.880 / 1.672 | 82.4 / 88.1 | 339.5 / 191.6 | 223.2 / 153.7 | 80.5 / 80.1 |

Each string Patricia map retained 8 words/binding, compared with 6 for AVL.
Patricia lookup remains slightly faster, but construction and mutations become
slower as keys lengthen, plausibly because routing and first-difference work
on string bytes.  The benchmark uses fixed-width alphanumeric keys, so it
does not establish behavior for arbitrary string distributions or long shared
prefixes.

| Key length | Disjoint union P / AVL (ms) | Disjoint allocation P / AVL | 50% overlap P / AVL (ms) | Overlap allocation P / AVL |
| --- | ---: | ---: | ---: | ---: |
| 3 | 0.754 / 0.004 | 429,098 / 2,404 | 0.505 / 0.083 | 425,586 / 81,324 |
| 4 | 0.765 / 0.004 | 429,098 / 2,404 | 0.526 / 0.074 | 425,586 / 81,324 |
| 5 | 0.779 / 0.005 | 429,098 / 2,404 | 0.574 / 0.080 | 425,586 / 81,324 |

The nearly constant Patricia union allocation across key lengths indicates
that rebuilding the tree, rather than the small change in string-key length,
dominates these measurements.

## Larger-input follow-up: 100,000 bindings

The same command was rerun with `PATRICIA_BENCH_SIZE=100000`.  All result
checks passed.  This size remains valid for the three-character data set,
which needs two disjoint 100,000-key ranges.

| Workload | Integer P / AVL | String P / AVL (range over 3--5 characters) |
| --- | ---: | ---: |
| Build | 9.116 / 18.042 ms | 22.557--30.653 / 18.234--18.516 ms |
| Lookup | 47.8 / 111.1 ns/op | 86.3--87.4 / 106.7--112.0 ns/op |
| Add fresh | 79.5 / 203.5 ns/op | 279.6--352.6 / 205.5--209.1 ns/op |
| Update | 102.9 / 186.6 ns/op | 239.9--258.5 / 186.1--196.4 ns/op |
| Remove | 29.5 / 107.6 ns/op | 104.6--106.0 / 99.4--102.7 ns/op |
| Disjoint union | 12.435 / 0.006 ms | 16.165--16.523 / 0.007--0.008 ms |
| 50% overlap union | 9.227 / 1.925 ms | 12.529--13.021 / 1.688--1.789 ms |

Retained size remained 8 words/binding for Patricia and 6 for AVL.  Integer
Patricia still wins lookup and ordinary mutations, while string Patricia
still wins lookup but loses most updates.  Per-operation lookup growth from
10,000 to 100,000 bindings was modest (integer Patricia: 44.7 to 47.8 ns;
string Patricia: 79--82 to 86--87 ns), as expected from bounded-depth Patricia
routing.  AVL lookup grew more noticeably (integer: 85.5 to 111.1 ns), which
is consistent with its logarithmic-height comparison path, but these two
measurements alone do not establish an asymptotic law.

Union remains the decisive scalability failure.  Patricia disjoint-union time
rose from 0.184 to 12.435 ms for integers and from roughly 0.77 to roughly
16.4 ms for strings; allocations rose from 200,364 to 3,468,125 words for
integers and from 429,098 to 4,289,171 words for strings.  The time increase
is larger than the 10x input increase because the additional allocation also
changes GC behavior, so it should not be read as a clean exponent.  It does,
however, reinforce the structural diagnosis: these unions traverse and rebuild
whole trees instead of preserving disjoint subtrees.  AVL disjoint union
remained about 0.006--0.008 ms and allocated only 3,620 words on this
ordered-disjoint input, indicating effective structural joining/sharing.

## Million-scale follow-up

Two further validated native runs measured one and ten million bindings per
input tree:

```sh
PATRICIA_BENCH_SIZE=1000000 PATRICIA_BENCH_STRING_LENGTHS=4,5 \
  make -C patricia benchmark
PATRICIA_BENCH_SIZE=10000000 PATRICIA_BENCH_STRING_LENGTHS=5 \
  make -C patricia benchmark
```

The 3-character space cannot represent the two disjoint one-million-key
inputs used by a benchmark, and the 4-character space cannot represent the
two disjoint ten-million-key inputs.  The string-length selector was added to
the benchmark for precisely this purpose; the ordinary default remains all
three lengths.

| Input size / keys | Build P / AVL | Lookup P / AVL | Add P / AVL | Update P / AVL | Remove P / AVL |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1M integers | 125.104 / 210.695 ms | 52.6 / 131.8 ns/op | 95.5 / 236.6 ns/op | 119.0 / 217.6 ns/op | 34.2 / 123.9 ns/op |
| 1M strings, 4 chars | 286.270 / 206.353 ms | 94.4 / 126.4 ns/op | 330.9 / 231.0 ns/op | 274.9 / 213.5 ns/op | 144.8 / 113.7 ns/op |
| 1M strings, 5 chars | 328.129 / 205.569 ms | 94.9 / 127.1 ns/op | 369.3 / 228.1 ns/op | 262.5 / 214.0 ns/op | 143.1 / 113.5 ns/op |
| 10M integers | 1,192.448 / 2,647.578 ms | 55.8 / 149.4 ns/op | 94.7 / 252.9 ns/op | 126.4 / 240.9 ns/op | 40.6 / 138.7 ns/op |
| 10M strings, 5 chars | 3,304.979 / 2,291.325 ms | 99.9 / 144.3 ns/op | 374.4 / 249.4 ns/op | 276.7 / 238.6 ns/op | 167.5 / 127.0 ns/op |

At both sizes, retained map size was stable at 8 words/binding for Patricia
and 6 for AVL.  The large inputs reinforce the earlier distinction: integer
Patricia wins ordinary operations by approximately 1.9x--3.4x, while direct
string Patricia retains a 1.3x--1.4x lookup advantage but is slower for build,
insert, update, and removal.

| Input size / keys | Disjoint union P / AVL | Disjoint allocation P / AVL | 50% overlap union P / AVL | Overlap allocation P / AVL |
| --- | ---: | ---: | ---: | ---: |
| 1M integers | 135.244 / 0.013 ms | 35,938,449 / 4,940 | 104.129 / 27.575 ms | 39,833,410 / 10,193,264 |
| 1M strings, 4 chars | 162.045 / 0.012 ms | 43,794,603 / 4,940 | 135.359 / 26.230 ms | 46,713,726 / 10,193,264 |
| 1M strings, 5 chars | 166.187 / 0.012 ms | 43,794,603 / 4,940 | 137.863 / 26.691 ms | 46,713,726 / 10,193,264 |
| 10M integers | 1,361.910 / 0.020 ms | 359,802,480 / 6,562 | 1,106.904 / 280.746 ms | 400,010,380 / 101,428,506 |
| 10M strings, 5 chars | 1,595.612 / 0.019 ms | 437,942,071 / 6,562 | 1,415.312 / 272.601 ms | 468,492,579 / 101,428,506 |

The million-scale data remove ambiguity from the small-run timing noise:
Patricia disjoint union grows roughly in proportion to input size once the
input is large (135 ms at 1M and 1.36 s at 10M for integer keys), and creates
roughly 36 heap words per integer input binding or 44 per string input binding.
AVL disjoint union remains near-constant on this ordered-disjoint workload,
at 0.012--0.020 ms and a few thousand words, because it can combine the two
ranges structurally.  At 10M, Patricia disjoint union is about 68,000x slower
for integers and 84,000x slower for strings, and allocates over 54,000x and
66,000x as many words, respectively.  This is compelling empirical evidence
that the generic fuel-and-rebuild implementation must not underlie biased
union.

## Baseline interpretation and completed follow-up

These numbers made specialized biased union the highest-priority performance
change.  That change is now implemented in both native extracted backends:
the generic native merge bypasses proof-side whole-tree fuel, and biased union
returns unchanged one-sided and disjoint subtrees wherever its left-bias
semantics permits.  The post-change 10,000- and 100,000-binding checks at the
top of this document confirm the expected allocation behavior.  Do not use
the absolute times as regression thresholds: they are affected by machine,
compiler, runtime, and GC state.
