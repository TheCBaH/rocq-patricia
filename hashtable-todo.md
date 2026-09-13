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
| Rocq implementation and proofs | H0 complete; H1 bitmap/dense-list and bucket source modules compile, with their full primitive proof gate still open |
| Reference OCaml extraction and public wrapper | Not started |
| Compact-array model, proofs and native backend | Not started |
| Tests, build/CI integration and benchmarks | Not started |

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

- [ ] **H1.1** In progress: `HashTableBits.v` defines chunks and proves the per-chunk bound; six-chunk reconstruction/separation remains open.
- [ ] **H1.2** In progress: `HashTableBits.v` defines bounded popcount/rank and dense-list edits, with slot-31/full-bitmap boundary lemmas; rank/edit correspondence proofs remain open.
- [ ] **H1.3** In progress: `HashTableBucket.v` defines lookup/set/remove and empty/singleton/many normalization with head replacement/removal lemmas; uniqueness and full pointwise laws remain open.
- [ ] **H1.G** Gate: primitive proofs compile and theorem assumption audit passes.

## H2 — Source HAMT

Dependencies: H1.G.

- [ ] **H2.1** In progress: `HashTable.v` defines raw nodes, seeded tables and an independent flattened `bindings` view; the well-formedness invariant remains open.
- [ ] **H2.2** In progress: `HashTable.v` implements bounded `join_worker`; validity/binding and unreachable-fallback proofs remain open.
- [ ] **H2.3** In progress: `HashTable.v` implements fuelled bitmap-routed `get_tree`; `HashTableProof.v` proves leaf/collision base cases. Independent binding equivalence remains open.
- [ ] **H2.4** In progress: `HashTable.v` implements persistent `set_tree` and the public seeded `set`; `HashTableProof.v` proves the leaf replacement/representative base case. Global pointwise and validity laws remain open.
- [ ] **H2.5** In progress: `HashTable.v` implements persistent `remove_tree` and retains unary branches; `HashTableProof.v` proves matching-leaf removal. Pointwise, validity and seed laws remain open.
- [ ] **H2.6** Prove branch-path height at most six and global key uniqueness.
- [ ] **H2.G** Gate: core laws kernel-checked; assumption audit and existing Patricia proof build pass.

## H3 — Reference release

Dependencies: H2.G.

- [ ] **H3.1** Add/prove singleton, emptiness, membership, first-wins of_list, elements and extensional equivalence.
- [ ] **H3.2** In progress: `HashTableReferenceExtract.v` regenerates a separately isolated list-source extraction. The public reference package name and bounded test-hash API remain open.
- [ ] **H3.3** In progress: `HashMap.mli` / `.ml` expose `HashMap.Make(Key)` over the reference extraction and normalize raw hashes with `land 0x3fffffff`. Callback/foreign-contract inventory and record example remain open.
- [ ] **H3.4** In progress: `HashTableReferenceTest.ml` exercises direct extracted source operations for controlled collisions, routing depths, first-wins values and retained roots. The public-functor oracle histories, custom equivalences and boundary matrix remain open.
- [ ] **H3.5** In progress: `HashMapTest.ml` compiles through the abstract wrapper and checks callback-instance isolation. A broader interface/extraction audit remains open.
- [ ] **H3.G** Gate: proved reference exports to OCaml; reference proof/audit/build/test subset passes from regenerated output.

## H4 — Compact-array backend

Dependencies: H3.G.

- [ ] **H4.1** Define persistent sequence interface and array/source representation relation; prove view laws.
- [ ] **H4.2** Prove native modeled get/set/remove refinement and invariant/seed preservation.
- [ ] **H4.3** Prove bounded bitmap/scalar/popcount workers including all native intermediate and shift bounds.
- [ ] **H4.4** Implement private fresh-copy array primitives and extraction bindings; document remaining target obligations.
- [ ] **H4.5** Audit generated map workers and primitive realizer inventory; reject high-level algorithm overrides.
- [ ] **H4.6** Run reference/native/oracle histories in bytecode and native code, including retained versions and function/reference payloads.
- [ ] **H4.7** Switch public wrapper to native backend after passing correctness and refinement gates.
- [ ] **H4.G** Gate: modeled refinement proofs and all native checks pass; foreign/heap trust remains accurately stated.

## H5 — Integration and evaluation

Dependencies: H4.G; benchmark harness may begin after H3.G.

- [ ] **H5.1** Integrate aggregate targets, assumption discovery, cleanup and CI without regressing Patricia.
- [ ] **H5.2** Add generic-key checked benchmarks against list reference, compatible Map.Make and Hashtbl instances; include StringPatriciaMap for string workloads.
- [ ] **H5.3** Record timing/allocation/retained heap with compiler, seed, key distributions and version-retention policy.
- [ ] **H5.4** In progress: README and design status now describe the source-reference milestone without claiming proof/native completion. Final supported API, theorem inventory and extraction boundary remain open.
- [ ] **H5.5** Run fresh full build and benchmark smoke; record local and hosted CI evidence separately.
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
| 2026-09-13 | H2.1–H2.5 (partial) | Added `HashTable.v`; `make hashtable-proof` passed. The source executes bounded bitmap-HAMT workers, provides an independent flattening/elements view and first-wins bulk loader, and proves empty/singleton basics. It has no established global invariant or pointwise update/removal proof yet. |
| 2026-09-13 | H3.2, H3.4 (partial) | Added `HashTableReferenceExtract.v` and `HashTableReferenceTest.ml`; `make hashtable-reference-test` regenerated, compiled and ran the reference extraction successfully. The deterministic test covers empty/singleton, constant-hash collisions, replacement, deletion, depths 0–4 routing, first-wins duplicate values and retained versions. It directly calls extracted source modules and does not yet validate the public functor. |
| 2026-09-13 | H3.3, H3.5 (partial) | Added `HashMap.mli`, `HashMap.ml` and `HashMapTest.ml`; `make hashtable-wrapper-test` passed. The abstract wrapper test covers negative normalized hashes, `min_int`/`max_int`, equivalent string and record-ID keys, first representative/value retention, retained versions, function/reference payloads and three simultaneous key modules. It remains a reference-backend test, not the H3 proof/audit gate. |
| 2026-09-13 | H2.1, H2.3–H2.5 (partial) | Added `HashTableProof.v`; `make hashtable-proof` passed. It kernel-checks collision-normalization binding preservation, empty-tree binding equations, matching/mismatching leaf lookup, collision dispatch, representative-preserving leaf replacement and leaf removal. Recursive routing and invariant proofs remain open. |
| 2026-09-13 | H5.4 (partial) | Updated README and design status to describe the tested source-reference milestone and open proof/native gates; `git diff --check` passed. |

Append subsequent evidence here with task IDs, theorem/source names, exact
commands, pass/fail results and remaining assumptions. Reopen a gate if its
supporting contract or implementation changes.
