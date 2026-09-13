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
| Rocq implementation and proofs | Not started |
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

- [ ] **H0.1** Add generic key-equivalence/seed/hash contracts, normalization proof and integer/string/record instances.
- [ ] **H0.2** Demonstrate positive recursive types, join termination and extraction shape; record native container strategy.
- [ ] **H0.3** Set up module dependencies and separate extraction directories; record actual Rocq/OCaml versions.
- [ ] **H0.G** Gate: compiling skeleton with explicit hypotheses and no admitted obligations.

## H1 — Primitive proofs

Dependencies: H0.G.

- [ ] **H1.1** Prove hash bounds, chunk bounds and six-chunk reconstruction/separation.
- [ ] **H1.2** Implement/prove bitmap rank and dense-list lookup/insert/replace/delete, including slot 31 and full bitmap.
- [ ] **H1.3** Implement/prove collision lookup/replacement/deletion, uniqueness and size normalization.
- [ ] **H1.G** Gate: primitive proofs compile and theorem assumption audit passes.

## H2 — Source HAMT

Dependencies: H1.G.

- [ ] **H2.1** Define nodes, flattened bindings and seed/depth/prefix well-formedness.
- [ ] **H2.2** Implement join; prove validity, preserved bindings and unreachable fuel fallback.
- [ ] **H2.3** Implement lookup and prove equivalence to flattened bindings.
- [ ] **H2.4** Implement set; prove pointwise law, validity and seed preservation.
- [ ] **H2.5** Implement remove; prove pointwise law, validity, seed preservation and unary-depth safety.
- [ ] **H2.6** Prove branch-path height at most six and global key uniqueness.
- [ ] **H2.G** Gate: core laws kernel-checked; assumption audit and existing Patricia proof build pass.

## H3 — Reference release

Dependencies: H2.G.

- [ ] **H3.1** Add/prove singleton, emptiness, membership, first-wins of_list, elements and extensional equivalence.
- [ ] **H3.2** Add pure bounded test hash; extract list reference with separately named modules.
- [ ] **H3.3** Add abstract HashMap.Make(Key) wrapper, hash normalization and string/integer/record examples; inventory callback and foreign contracts.
- [ ] **H3.4** Add equality-based oracle histories, controlled collisions, generic keys/custom equivalences, representative retention, normalized-hash edge cases, full native int boundaries and retained-root tests.
- [ ] **H3.5** Compile wrapper clients and verify that constructors, per-operation hashes, depth and fuel remain private; supplied callbacks stay bound to their functor instance.
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
- [ ] **H5.4** Update supported API specification, theorem inventory, extraction boundary and README usage.
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

Append subsequent evidence here with task IDs, theorem/source names, exact
commands, pass/fail results and remaining assumptions. Reopen a gate if its
supporting contract or implementation changes.
