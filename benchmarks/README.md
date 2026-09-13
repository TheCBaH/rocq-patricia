# Native string-worker acceptance

The `StringBits*.ml` files are benchmark fixtures. They are copied into isolated
temporary builds by `make string-worker-performance`; production extraction
never imports them. `StringBitsBaseline.ml` preserves the handwritten bodies
from `e7f5cd6:PatriciaExtract.v`. All other map code, wrappers, compiler settings
and workloads are shared between each comparison build.
Every binding fixture declares the same two module aliases and four values,
so unchanged primitives use the same historical unit and dependency order.
The control uses `StringBitsHistorical.ml`; it does not duplicate the baseline
algorithm bodies inside a second runtime unit.

| Variant | Packed bit | Bounded prefix | First difference |
| --- | --- | --- | --- |
| Baseline | Historical | Historical | Historical |
| Bit | Generated | Historical | Historical |
| Prefix | Historical | Generated | Historical |
| Diff | Historical | Historical | Generated |
| All | Generated | Generated | Generated |

Run the full matrix with:

```sh
PATRICIA_STRING_ROUNDS=5 PATRICIA_BENCH_SHORT_BATCH=8 make string-worker-performance
```

The script prints its artifact directory, retaining source hashes, toolchain
and workload settings, native binaries and every result log. It alternates
variant order between rounds. The default sizes are 10K and 100K, with fixed
four-byte, variable-length and 192-byte-common-prefix keys. Workloads cover
build/random build, lookup, membership, updates, deletion, combine, and both
union biases, including separately allocated equal maps. Inputs are created
outside each operation's measurement. AVL/hash results remain correctness
oracles; their timing repetition is reduced for this acceptance run.

Summarize the printed directory with:

```sh
python3 benchmarks/summarize-string-workers.py /tmp/patricia-string-acceptance.EXAMPLE
python3 benchmarks/summarize-string-workers.py /tmp/patricia-string-acceptance.EXAMPLE --csv
```

The summary requires at least three completed samples for every reported
workload. It flags disjoint timing ranges and allocation growth for
investigation; it does not automatically declare acceptance. Sub-clock
readings, GC promotion, unrelated implementation changes and the final
selected combination must be assessed explicitly.

`make string-primitive-profile` independently compares the generated workers
and selected bindings against the frozen baseline and proof-aligned oracle.
Its seven timing samples alternate baseline/candidate order, with pre-created
inputs, warmups and consumed results. See [the tracker](../patricia-str-tood.md)
and [measurement record](../patricia-bench.md) for decisions and evidence.
