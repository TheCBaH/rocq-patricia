# Reference hash-table release inventory

This records the H3 source-reference boundary. The Rocq-extracted, list-backed
HAMT remains available as the separately tested `HashTableReference` package.
`HashMap.Make` now uses the H4 generated native table backend under the same
abstract map type; its array/view contract is recorded separately in the H4
tracker.

## Boundary and external contracts

| Boundary | Contract / evidence | Status |
| --- | --- | --- |
| Source map semantics | `HashTableProof.v` proves validity, flattened-binding lookup, set/remove equations, enumeration uniqueness, seed preservation, and first-wins lookup under explicit equivalence, reflection, hash-congruence, and bounded-hash hypotheses. | Kernel-checked; `hashtable-assumptions` rejects open assumptions. |
| Extraction and public surface | `HashTableReferenceExtract.v` extracts source workers for the direct reference package. `HashTableNativeArrayExtract.v` binds only native `pseq` to private fresh-copy arrays for the public wrapper. `HashTableReference.mli` and `HashMap.mli` hide constructors, depth, routing hashes, and raw callbacks. Generated-interface, reference-boundary, and native-array extraction audits cover these surfaces. | Generated code and interface audit; array implementation contract is foreign. |
| Machine integers and normalization | The wrapper computes `raw land 0x3fffffff`, so callbacks may return any OCaml `int` and routing receives a nonnegative 30-bit value. This relies on OCaml `int` bitwise semantics and the compiler/runtime executing the generated code as specified. Extreme negative and large raw hashes are tested in `HashMapTest.ml`; deterministic source test hashes are in `HashTableTestHash.ml`. | Foreign runtime contract; finite bytecode/native evidence. |
| Key callbacks | `Key.equal` must implement an equivalence relation. Equivalent keys must have the same normalized hash for each seed, and callbacks must be stable for a map's lifetime. The functor binds callbacks to its map instance. | Client contract stated in `HashMap.mli`; equivalent-key and multi-instance tests provide finite evidence. |
| Persistence and payloads | Source maps use immutable Rocq trees/lists; update and removal return new roots. Values are never compared and are shallowly shared, so mutation through a retrieved reference remains observable. | Source algorithms are kernel-checked; OCaml allocation/immutability and payload identity are runtime contracts, with retained-version and mutable-payload tests. |
| Native arrays | `HashTablePrimitives.ml` is private H4 code, not part of the H3 source-reference implementation. Its array, bounds, and fresh-allocation obligations remain separately inventoried and audited by native targets. | Out of the H3 reference boundary. |

## Reference test matrix

`HashTableReferenceTest.ml` runs from regenerated extraction in bytecode.
`HashMapTest.ml` and `HashTableDifferentialTest.ml` run through the public
wrapper in both bytecode and native code via the targets named below.

| Required case | Coverage |
| --- | --- |
| Empty, singleton, replacement, missing removal | `HashTableReferenceTest.ml`: `empty`, `one`, collision replacement/removal; `HashMapTest.ml`: public update/removal cases. |
| Constant hash, many keys, collision normalization | `HashTableReferenceTest.ml`: three constant-hash keys, update, deletion; `HashMapTest.ml`: normalized raw collision. |
| First difference at depths 0–5 | `HashTableReferenceTest.ml`: `routed` keys `0; 1; 32; 1024; 32768; 1048576; 33554432`. |
| Slot 31 and all 32 children | `HashTableReferenceTest.ml`: `every_slot`, including deletion of slot 31. |
| Delete to unary, then insert again | `HashTableReferenceTest.ml`: `unary_after_remove` / `unary_reinserted` for `0` and `32`. |
| Integer, record, and byte-string boundaries | `HashMapTest.ml`: negative/minimum/maximum integers, record-ID keys, and empty/NUL/high-byte/long-prefix strings. |
| Custom equivalence and resident representatives | `HashMapTest.ml`: case-folded and record-ID keys; `HashTableDifferentialTest.ml`: 500-step folded-key history. |
| Raw-hash extremes and independent callbacks | `HashMapTest.ml`: `Extreme_hash_key`; separate integer, byte, case-folded, and record functor instances. |
| Duplicate/equivalent bulk input | `HashTableReferenceTest.ml`: direct duplicate values; `HashMapTest.ml`: case-folded `of_list`, including representative. |
| Seeds and retained versions | `HashMapTest.ml`: retained update/removal history; `HashTableDifferentialTest.ml`: 1,000 integer and 500 folded-key retained histories with separate seeds. |
| Mutable references and functions | `HashMapTest.ml`: function-valued record update and mutable-reference payload identity; `HashTableDifferentialTest.ml`: function-valued folded history. |
| Deterministic oracle histories | `HashMapTest.ml` compares an association-list oracle; `HashTableDifferentialTest.ml` compares `Stdlib.Map` for integer and folded-key histories. |

Validation commands for this matrix are:

```sh
make hashtable-reference-test hashtable-wrapper-test hashtable-wrapper-test-native \
  hashtable-differential hashtable-test-native
```
