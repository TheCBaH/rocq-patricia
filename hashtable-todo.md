# Persistent generic hash table: tracker

Last updated: 2026-09-13.

Contract: [hashtable-design.md](hashtable-design.md). Delivery gates and proposed
files/commands: [hashtable-plan.md](hashtable-plan.md). Background:
[hashtable.md](hashtable.md). This tracker does not change Patricia task status.

`[x]` means completed with evidence, `[ ]` means open. Deferred work is listed
separately. Close implementation tasks only with source/theorem references,
validation command, result and date. Proposed theorem names or targets in the
planning documents are not evidence that code exists.

## Current state

| Deliverable | State |
| --- | --- |
| Design, implementation plan and tracker | Written; documentation checks recorded below |
| Rocq implementation and proofs | H0 complete; H1–H3 source/reference foundations and modeled H4 refinement compile, while their recursive/global proof gates remain open |
| Reference OCaml extraction and public wrapper | Separately regenerated list-source extraction and abstract `HashMap.Make` wrapper build and pass direct/wrapper tests; full H3 proof gate remains open |
| Compact-array model, proofs and native backend | Modeled persistent sequence/refinement and tested fresh-copy OCaml primitives exist; extraction bindings, native map realization and public switch remain open |
| Tests, build/CI integration and benchmarks | Implemented aggregate, CI steps, direct/wrapper/native primitive tests and checked benchmark smoke; broader native differential and release evidence remain open |

## Documentation baseline

- [x] **D1** Select representation, hash width, seed policy and collision rules.
- [x] **D2** Specify public API, map laws, invariants and proof boundary.
- [x] **D3** Define delivery gates, proposed modules and validation matrix.
- [x] **D4** Link documents from the investigation and README; check links and whitespace.

- [x] **D5** Compare HAMT/CHAMP runtime tradeoffs and Rocq proof obligations; record source evidence and the HAMT-first decision.
- [x] **D6** Generalize the public API to HashMap.Make(Key); specify equivalence/hash laws, normalization, representatives and stable-key requirements.

## H0 — Contract and skeleton

Dependencies: documentation baseline.

- [x] **H0.1** `HashTableSpec.v` defines explicit equivalence/reflection and hash-congruence contracts; `normalize_hash` is bounded by `2^30`, including checked negative boundary hashes, with Z/string/record-ID instances.
- [x] **H0.2** `HashTableSkeleton.v` demonstrates strictly-positive list children and fuel-decreasing `join_worker`/`update_worker`; `HashTableSkeletonExtract.v` confirms callbacks and fuel survive reference extraction. H1 retains this list source shape; H4 will relate private fresh-copy arrays to it.
- [x] **H0.3** `Makefile` adds H0 proof/extraction targets and `hashtable_reference_extracted/` / `hashtable_extracted/` are ignored separately from Patricia output. Toolchain recorded: Rocq 9.2, OCaml 4.14.3.
- [x] **H0.G** Gate: skeleton compiles, extracts, and its theorem assumptions are closed under the global context.

## H1 — Primitive proofs

Dependencies: H0.G.

- [ ] **H1.1** In progress: `HashTableBits.v` defines chunks, proves the per-chunk bound and proves a normalized 30-bit hash has zero chunk at depth six; six-chunk reconstruction/separation remains open.
- [ ] **H1.2** In progress: `HashTableBits.v` defines bounded popcount/rank and dense-list edits, with slot-31/full-bitmap boundary calculations, full occupied-slot enumeration, bounded lookup laws before/at/after insertion plus replacement/removal lookup preservation, and insertion/replacement/deletion membership laws; general bitmap-rank correspondence remains open.
- [ ] **H1.3** In progress: `HashTableBucket.v` defines lookup/set/remove and empty/singleton/many normalization with head replacement/removal and exact miss-insertion/cardinality lemmas; uniqueness and full pointwise laws remain open.
- [ ] **H1.G** Gate: primitive proofs compile and theorem assumption audit passes.

## H2 — Source HAMT

Dependencies: H1.G.

- [ ] **H2.1** In progress: `HashTable.v` defines raw nodes, seeded tables and an independent flattened `bindings` view; `HashTableProof.v` now defines the hash/prefix, collision-uniqueness and bitmap/dense-child well-formedness invariant. Its preservation proofs remain open.
- [ ] **H2.2** In progress: `HashTable.v` implements bounded `join_worker`; `HashTableProof.v` proves flattened binding union for both `join_two` and every fuelled worker path, including the fallback. Validity and unreachable-fallback routing proofs remain open.
- [ ] **H2.3** In progress: `HashTable.v` implements fuelled bitmap-routed `get_tree`; `HashTableProof.v` proves matching/mismatching leaf and collision base cases, normalized same-hash collision lookup and zero-fuel branch fallback. Independent binding equivalence and fallback unreachability remain open.
- [ ] **H2.4** In progress: `HashTable.v` implements persistent `set_tree` and the public seeded `set`; `HashTableProof.v` proves leaf replacement/representative, same-hash collision insertion/lookup, distinct-hash leaf and branch insertion/replacement binding, zero-fuel branch fallback, and `set_seed` base cases. Global pointwise and validity laws remain open.
- [ ] **H2.5** In progress: `HashTable.v` implements persistent `remove_tree` and retains unary branches; `HashTableProof.v` proves matching/mismatching leaf removal, same-hash collision removal/miss preservation, branch-removal binding subset, zero-fuel branch fallback and `remove_seed`. Pointwise and validity laws remain open.
- [ ] **H2.6** Prove branch-path height at most six and global key uniqueness.
- [ ] **H2.G** Gate: core laws kernel-checked; assumption audit and existing Patricia proof build pass.

## H3 — Reference release

Dependencies: H2.G.

- [ ] **H3.1** In progress: `HashTable.v` now proves empty/singleton emptiness, singleton membership/removal and enumeration, singleton bulk loading, and duplicate-singleton first-wins lookup/enumeration; general pointwise first-wins and extensional laws remain open.
- [ ] **H3.2** In progress: `HashTableReferenceExtract.v` regenerates a separately isolated list-source extraction, while `HashTableReference.ml` / `.mli` provide its stable package name. The bounded test-hash API remains open.
- [ ] **H3.3** In progress: `HashMap.mli` / `.ml` expose `HashMap.Make(Key)` over `HashTableReference` and normalize raw hashes with `land 0x3fffffff`. Callback/foreign-contract inventory and record example remain open.
- [ ] **H3.4** In progress: direct and public-wrapper tests exercise controlled collisions, routing depths, first-wins values, retained roots, a 500-step association-list-oracle history, and a 1,000-step `Stdlib.Map` differential history in bytecode/native code. The broader custom-equivalence and boundary matrix remains open.
- [ ] **H3.5** In progress: `HashMapTest.ml` compiles through the abstract wrapper and checks callback-instance isolation. `hashtable-extraction-audit` verifies abstract public types, hidden routing internals and functor-bound normalized callbacks; a generated-interface audit remains open.
- [ ] **H3.G** Gate: proved reference exports to OCaml; reference proof/audit/build/test subset passes from regenerated output.

## H4 — Compact-array backend

Dependencies: H3.G.

- [ ] **H4.1** In progress: `HashTableNative.v` defines a source-modeled persistent sequence interface, fresh-update view laws and a native-tree/source relation with empty/leaf/collision refinement lemmas; `HashTableExtract.v` compiles a separately extracted modeled-native artifact. Array realization and recursive branch refinement remain open.
- [ ] **H4.2** In progress: `HashTableNative.v` / `HashTableNativeProof.v` define modeled native get/set/remove and prove refinement for arbitrary related source/native trees; the separately extracted model passes a retained-version differential test against extracted source workers. Invariant/seed preservation and any array-realizer refinement remain open.
- [ ] **H4.3** Prove bounded bitmap/scalar/popcount workers including all native intermediate and shift bounds.
- [ ] **H4.4** In progress: `HashTablePrimitives.ml` / `.mli` provide private fresh-copy sequence primitives and `HashMapNative.ml` uses them for a private-array HAMT; primitive and reference/native differential tests validate views, storage freshness and map behavior. Extraction bindings and their full target inventory remain open.
- [ ] **H4.5** In progress: `hashtable-native-primitives-audit` inventories the current private sequence realizer and rejects map overrides/unsafe escapes; generated map-worker and extraction-binding audit remain open.
- [ ] **H4.6** In progress: `hashtable-native-array-test` and `hashtable-native-array-test-native` run retained-version reference/native histories in bytecode/native code. Broader payload/custom-key coverage remains open.
- [ ] **H4.7** Switch public wrapper to native backend after passing correctness and refinement gates.
- [ ] **H4.G** Gate: modeled refinement proofs and all native checks pass; foreign/heap trust remains accurately stated.

## H5 — Integration and evaluation

Dependencies: H4.G; benchmark harness may begin after H3.G.

- [ ] **H5.1** In progress: `make hashtable` aggregates the implemented proof/audit/reference/wrapper/primitive gates, clean removes its generated outputs, and CI invokes it under the existing pinned toolchain. Hosted result and completion of the remaining gates are open.
- [ ] **H5.2** In progress: `HashTableBenchmark.ml` supplies a checked integer-key native benchmark against an association-list oracle, `Map.Make` and `Hashtbl`; string/`StringPatriciaMap` workloads and broader generic instances remain open.
- [ ] **H5.3** Record timing/allocation/retained heap with compiler, seed, key distributions and version-retention policy.
- [ ] **H5.4** In progress: README and design status now describe the source-reference milestone without claiming proof/native completion. Final supported API, theorem inventory and extraction boundary remain open.
- [ ] **H5.5** In progress: local clean aggregate and hash-table benchmark smoke pass; CI is configured to run the smoke separately. Hosted results remain open.
- [ ] **H5.G** Gate: all required deliverables exist and release claims match proof and runtime evidence.

## Deferred scope

CHAMP layout/refinement; skip/prefix nodes; custom 64-bit hashing; 32-bit OCaml
port; map/merge/union/fold extensions; ordered or
standard-library-compatible API; cryptographic collision protection; formal
expected-cost/allocation proofs; full OCaml heap/compiler verification; mandatory
physical identity reuse for unchanged updates. Each needs its own design and
acceptance criteria before adding it to the current release.

## Validation log

| Date | Items | Evidence / result |
| --- | --- | --- |
| 2026-09-13 | D1–D3 | Reviewed hashtable.md, Patricia source/extractors, StringPatriciaMap.mli, Makefile and assumption audit; wrote design and staged plan. Confirmed local OCaml hash.c uses the 30-bit mask. No implementation/proof completion claimed. |
| 2026-09-13 | D5 | Reviewed the original CHAMP paper; added the design comparison and benchmark-controlled revisit criteria. OCaml speed and proof-effort judgments are explicitly prospective. |
| 2026-09-13 | D6 | Corrected scope to arbitrary lawful key types; updated design, plan, tracker, investigation and README. Documentation link/whitespace checks passed; implementation gates remain open. |
| 2026-09-13 | D4 | Checked relative Markdown file links in the new documents and README/investigation additions; `git diff --check` passed. |
| 2026-09-13 | H0.1–H0.G | Added `HashTableSpec.v`, `HashTableSkeleton.v`, `HashTableSkeletonExtract.v`, separate paths and H0 Make targets. `make hashtable-proof hashtable-skeleton-extraction` passed with Rocq 9.2 / OCaml 4.14.3. Printed assumptions for all 14 H0 lemmas: every result was `Closed under the global context`. Generated `HashTableSkeleton.ml` retains `eqb0`, `fuel`, `full_hash`, key and value arguments in `update_worker`. |
| 2026-09-13 | H1.1–H1.3 (partial) | Added `HashTableBits.v` and `HashTableBucket.v`; `make hashtable-proof hashtable-skeleton-extraction` and compilation of the generated reference modules passed. Primitive evidence currently covers chunk bounds, a 32-step popcount/rank bound, slot 31/full bitmap checks, dense edit sizes, bucket self-update/miss/removal behavior and normalization cases. It does not close the H1 gate. |
| 2026-09-13 | H2.1–H2.5 (partial) | Added `HashTable.v`; `make hashtable-proof` passed. The source executes bounded bitmap-HAMT workers, provides an independent flattening/elements view and first-wins bulk loader, and proves empty/singleton basics plus seed preservation for set/remove/singleton/bulk load. It has no established global invariant or pointwise update/removal proof yet. |
| 2026-09-13 | H3.2, H3.4 (partial) | Added `HashTableReferenceExtract.v` and `HashTableReferenceTest.ml`; `make hashtable-reference-test` regenerated, compiled and ran the reference extraction successfully. The deterministic test covers empty/singleton, constant-hash collisions, replacement, deletion, first hash differences at depths 0–5, all 32 root slots including slot-31 deletion, first-wins duplicate values and retained versions. It directly calls extracted source modules and does not yet validate the public functor. |
| 2026-09-13 | H3.1, H3.3–H3.5 (partial) | Added `HashMap.mli`, `HashMap.ml` and `HashMapTest.ml`; `make hashtable-wrapper-test` and `make hashtable-wrapper-test-native` passed. Source lemmas cover basic emptiness/membership/empty bulk loading. The abstract wrapper test covers negative normalized hashes, `min_int`/`max_int`, empty/NUL/high-byte/prefix-NUL/long strings, equivalent string and record-ID keys, first representative/value retention, retained versions, function/reference payloads, four simultaneous key modules, and a 500-step deterministic association-list-oracle history with sampled retained versions. It remains a reference-backend test, not the H3 proof/audit gate. |
| 2026-09-13 | H2.1, H2.3–H2.5 (partial) | Added `HashTableProof.v`; `make hashtable-proof` passed. It kernel-checks collision-normalization binding preservation, empty-tree binding equations, matching/mismatching leaf lookup, collision dispatch, representative-preserving leaf replacement and leaf removal. Recursive routing and invariant proofs remain open. |
| 2026-09-13 | H5.4 (partial) | Updated README and design status to describe the tested source-reference milestone and open proof/native gates; `git diff --check` passed. |
| 2026-09-13 | H1.2 (partial) | Added bounded same-index `dense_get` laws for insertion and replacement in `HashTableBits.v`; `make hashtable-proof` passed. Bitmap/rank correspondence is still open. |
| 2026-09-13 | H2.1 (partial) | Defined the parameterized `wf` invariant in `HashTableProof.v`, including occupied-slot ordering, bitmap/popcount density, prefix/hash routing, nonempty branch children and collision uniqueness. Empty/leaf root constructors and prefix-extension routing lemma are kernel-checked; `make hashtable-proof` passed. Preservation and lookup-refinement proofs remain open. |
| 2026-09-13 | H1.G/H2.G support (partial) | Added `check-hashtable-assumptions.sh`; `make hashtable-assumptions` audited all 56 current hash-table theorem declarations as closed under the global context. This audit does not close the still-incomplete H1/H2 proof gates. |
| 2026-09-13 | H3.5 (partial) | Added `check-hashtable-extraction-boundary.sh`; `make hashtable-extraction-audit` passed, confirming an abstract public map type, no exposed routing representation/workers, and wrapper-owned 30-bit normalization with functor-bound callbacks. |
| 2026-09-13 | H4.1 (partial) | Added `HashTableNative.v`; `make hashtable-proof` passed. It provides modeled persistent-sequence view laws and base source refinement lemmas, without an OCaml array realizer or native operation-refinement claim. |
| 2026-09-13 | H4.2 (partial) | Added modeled native get/set/remove in `HashTableNative.v` and arbitrary-relation refinement lemmas in `HashTableNativeProof.v`; `make hashtable-proof hashtable-assumptions` passed with 76 theorem declarations closed. The model does not yet claim array realization, heap safety, invariant preservation or public-backend switching. |
| 2026-09-13 | H4.4 (partial) | Added `HashTablePrimitives.ml` / `.mli` and `HashTablePrimitivesTest.ml`; `make hashtable-native-primitives-test` passed through `ocamlopt`. It checks insert/replace/remove views, out-of-range behavior, fresh storage for all updates and unchanged retained storage. No extraction binding or full native-map realization is claimed. |
| 2026-09-13 | H5.1 (partial) | Added `make hashtable`, cleanup rules and a CI hash-table step. A local `make clean && make hashtable` regenerated all reference output and passed the proof, 68-theorem audit, extraction-boundary, direct reference, wrapper bytecode/native and primitive tests. A monitored fresh `make` then exited 0 with Patricia randomized, union and optimized/reference differential tests passing. A later local `make clean && make hashtable` passed the expanded 116-declaration audit, source/native-model bytecode/native differential tests, wrapper tests, primitive audit and tests from regenerated outputs. Hosted CI has not run in this tracker. |
| 2026-09-13 | H5.2 (partial) | Added `HashTableBenchmark.ml`; `make hashtable-benchmark-smoke` passed through `ocamlopt` with 100 bindings. It checked all wrapper/`Map.Make`/`Hashtbl` lookup results against an association-list oracle before reporting times and allocation bytes. Measurements are local workload evidence only. |
| 2026-09-13 | H1.2 (partial) | Added full-bitmap `popcount32`, slot-31 rank and occupied-slot enumeration lemmas in `HashTableBits.v`; `make hashtable-proof hashtable-assumptions` passed with 79 declarations closed. General bitmap/rank correspondence remains open. |
| 2026-09-13 | H1.2 (partial) | Added dense-child lookup preservation before/after insert, replacement off the edited index, and removal before/after the edited index. `make hashtable-proof hashtable-assumptions` passed with 84 declarations closed. General bitmap/rank correspondence remains open. |
| 2026-09-13 | H1.3 (partial) | Added exact collision-bucket miss insertion and its cardinality law under an explicit reflected-equality miss condition. `make hashtable-proof hashtable-assumptions` passed with 86 declarations closed. Bucket uniqueness and general pointwise laws remain open. |
| 2026-09-13 | H2.3/H2.4 (partial) | Added same-hash collision normalization, set-binding and lookup-after-set base laws in `HashTableProof.v`, using the explicit bucket miss/equality conditions. `make hashtable-proof hashtable-assumptions` passed with 90 declarations closed. Recursive routing and global pointwise/validity laws remain open. |
| 2026-09-13 | H2.5 (partial) | Added same-hash collision removal and miss-preservation binding laws in `HashTableProof.v`, using the explicit bucket miss condition. `make hashtable-proof hashtable-assumptions` passed with 92 declarations closed. Recursive routing and global pointwise/validity laws remain open. |
| 2026-09-13 | H3.1 (partial) | Added public singleton removal and resulting emptiness laws in `HashTable.v`. `make hashtable-proof hashtable-assumptions` passed with 94 declarations closed. Pointwise first-wins, enumeration and extensional laws remain open. |
| 2026-09-13 | H4.5 (partial) | Added `check-hashtable-primitives.sh` and `make hashtable-native-primitives-audit`; it checks the current private array-sequence realizer for fresh update allocation and rejects map overrides or unsafe escapes. Generated native map workers and extraction bindings do not yet exist and remain unaudited. |
| 2026-09-13 | H1.1 (partial) | Added `chunk_after_hash_bits_zero` in `HashTableBits.v`: every hash below `2^30` shifts to zero at depth six. `make hashtable-proof hashtable-assumptions` passed with 95 declarations closed. Six-chunk reconstruction and separation remain open. |
| 2026-09-13 | H3.1 (partial) | Added singleton bulk-loading and duplicate-singleton first-wins laws in `HashTable.v`. `make hashtable-proof hashtable-assumptions` passed with 97 declarations closed. General pointwise first-wins, enumeration and extensional laws remain open. |
| 2026-09-13 | H2.2 (partial) | Added flattened binding-union theorems for `join_two` and `join_worker`, including the fuel-zero fallback. `make hashtable-proof hashtable-assumptions` passed with 100 declarations closed. Validity and unreachable-fallback routing proofs remain open. |
| 2026-09-13 | H2.4 (partial) | Added the distinct-hash leaf-update binding characterization in `HashTableProof.v`, deriving exact old/new membership from the join binding theorem. `make hashtable-proof hashtable-assumptions` passed with 101 declarations closed. Recursive routing, global pointwise and validity laws remain open. |
| 2026-09-13 | H1.2 (partial) | Added exact dense-insertion membership and dense-removal membership-subset laws in `HashTableBits.v`. `make hashtable-proof hashtable-assumptions` passed with 103 declarations closed. General bitmap/rank correspondence remains open. |
| 2026-09-13 | H2.4 (partial) | Added dense-child-to-branch insertion binding preservation in `HashTableProof.v`: the result contains exactly the new child's bindings plus the prior branch bindings. `make hashtable-proof hashtable-assumptions` passed with 105 declarations closed. Recursive routing, global pointwise and validity laws remain open. |
| 2026-09-13 | H2.5 (partial) | Added dense-child-to-branch removal binding-subset preservation in `HashTableProof.v`: branch removal introduces no flattened bindings. `make hashtable-proof hashtable-assumptions` passed with 107 declarations closed. Recursive routing, global pointwise and validity laws remain open. |
| 2026-09-13 | H2.3/H2.5 (partial) | Added same-hash leaf key-miss lookup and removal-preservation laws in `HashTableProof.v`. `make hashtable-proof hashtable-assumptions` passed with 109 declarations closed. Recursive routing, global pointwise and validity laws remain open. |
| 2026-09-13 | H3.2/H3.3/H3.5 (partial) | Added the stable `HashTableReference` package over regenerated source extraction and routed `HashMap.Make` through it. Bytecode/native wrapper tests passed; the extraction-boundary audit now rejects direct generated-module use. The bounded test-hash API, callback inventory and record example remain open. |
| 2026-09-13 | H1.2/H2.4 (partial) | Added valid-index dense-replacement membership and its branch-binding lift: resulting branch bindings come from the replacement child or the prior branch. `make hashtable-proof hashtable-assumptions` passed with 111 declarations closed. General bitmap/rank correspondence, recursive routing and global validity remain open. |
| 2026-09-13 | H3.4 (partial) | Added `HashTableDifferentialTest.ml`, `make hashtable-differential` and `make hashtable-test-native`. Both bytecode/native tests passed 1,000 deterministic set/remove steps against `Stdlib.Map`, checking current and sampled retained versions across `min_int`, `max_int` and bounded keys. This exercises the reference wrapper only; a compact native-map differential remains open. |
| 2026-09-13 | H2.3–H2.5 (partial) | Added explicit zero-fuel branch equations for get/set/remove in `HashTableProof.v`. `make hashtable-proof hashtable-assumptions` passed with 114 declarations closed. The invariant proof that valid six-level routing never reaches these fallbacks remains open. |
| 2026-09-13 | H3.1 (partial) | Added enumeration laws for singleton removal and duplicate-singleton first-wins bulk loading in `HashTable.v`. `make hashtable-proof hashtable-assumptions` passed with 116 declarations closed. General pointwise first-wins and extensional laws remain open. |
| 2026-09-13 | H4.1 (partial) | Added `HashTableExtract.v` and `make hashtable-native` to extract and compile the source-defined modeled native operations in `hashtable_extracted/`. No array binding, recursive native branch realization or OCaml heap claim is made. |
| 2026-09-13 | H4.2 (partial) | Added `HashTableNativeModelTest.ml`, `make hashtable-native-model-test` and `make hashtable-native-model-test-native`. The regenerated extracted native model passed 750 deterministic set/remove steps in bytecode/native code, comparing source/native lookup results for current and sampled retained versions. This is model/extraction evidence only; it does not test an array-backed native map. |
| 2026-09-13 | H4.4/H4.6 (partial) | Added private-array `HashMapNative.Make` and `HashMapNativeTest.ml`, plus bytecode/native differential targets. Bytecode passed 1,000 deterministic reference/native set/remove steps with retained versions, collision-heavy keys, `min_int`/`max_int` and first-wins bulk loading. The public wrapper is unchanged and no kernel proof of this OCaml heap implementation is claimed. |

Append subsequent evidence here with task IDs, theorem/source names, exact
commands, pass/fail results and remaining assumptions. Reopen a gate if its
supporting contract or implementation changes.
