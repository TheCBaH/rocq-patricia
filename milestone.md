# Patricia implementation milestones

Last updated: 2026-08-29

This tracker turns the open items in `patricia.md`, `patricia-str.md`, and
`patricia-bench.md` into an implementation sequence.  Work starts with small,
independently checkable runtime improvements before the larger string-merge
proof and extraction-boundary projects.

Status legend: **done**, **in progress**, **next**, **later**.

## M1: Small runtime and validation improvements

- **done**: implement direct, allocation-free `mem` traversals for the
  integer and string maps, prove agreement with `get`, and benchmark present
  and absent membership.
- **done**: convert `elements` to an accumulator traversal in both maps, retain
  the existing traversal-order laws, and add a checked `elements` benchmark.
- **done**: preserve physical identity for absent removals with a source-level
  worker that reports whether anything changed; prove lookup and
  well-formedness preservation and check extracted physical identity.
- **done**: add checked generic-`combine` workloads and fuse its leaf/tree
  mapping and replacement passes.

Each M1 item passed `make`, the deterministic oracle test, and the native
benchmark. Performance observations are evidence, not machine-independent
thresholds.

## M2: Remove the remaining string-union allocation hotspot

- **done**: define a bounded `agrees_before` scanner in `StringBits.v`.
- **done**: prove its exact prefix specification and equivalence to logical
  `agrees_before`.
- **done**: provide and document the packed-token native realization, with an
  exhaustive one-byte/valid-split differential oracle.
- **done**: rerun the 10K and 100K half-overlap allocation measurements and
  update `patricia-bench.md`.

## M3: Complete direct-string functional proofs

- **done**: prove the equal-split, containment, and disjoint-prefix lemmas
  needed by merge.
- **next**: prove `combine_fuel` lookup correctness and well-formedness.
- **later**: lift the result to public `combine` under
  `f None None = None`.
- **later**: derive left- and right-biased union laws.
- **later**: add string extensional equality/`beq`, documented `elements`
  ordering, and finite-map extensionality theorems.

## M4: Harden the public extracted API

- **later**: generate an internal module and expose abstract map types through
  a handwritten wrapper interface.
- **later**: validate native integer keys and hide constructors, fuel, packed
  split tokens, and proof-internal helpers.
- **later**: document and enforce the public `combine` contract.
- **later**: retain a proof-aligned extraction backend for differential tests.

## M5: Reduce the trusted native-refinement boundary

- **later**: formalize the finite-width integer and packed string-position
  representation relations.
- **later**: strengthen the string invariant with cached-sample residency.
- **later**: replace handwritten direct `set`, `combine`, and biased-union
  realizers with proved source-level workers or prove their refinements.
- **later**: run `Print Assumptions` for every exported correctness theorem in
  automated validation.

## Validation log

- **2026-08-29 — direct membership and accumulator traversal**:
  `make` passed all Rocq compilation, extraction, OCaml compilation, and the
  deterministic randomized oracle test. `make benchmark` completed with
  `Patricia comparison benchmark: ok` at 10,000 bindings.
- Mixed membership performed 60,000 present/absent checks with 61 allocated
  words of fixed measurement overhead. The observed Patricia times were
  24.0 ns/op for integer keys and 63.1 ns/op for four-character keys.
- `elements` allocated 60,026 words for 10,000 bindings in both variants,
  matching `Stdlib.Map.bindings`; observed times were 3.8 ns/binding for
  integers and 2.9 ns/binding for four-character strings.
- **2026-08-29 — identity-preserving absent removal**: `make proof`, `make`,
  the deterministic randomized oracle test, and `make benchmark` passed.
  Both extracted maps returned the physically identical root after 10,000
  failed deletions and allocated only 26 words of measurement overhead.
- The focused absent-removal times were 12.3 ns/op for integer keys and
  17.1 ns/op for four-character string keys, versus 88.2 and 84.4 ns/op for
  `Stdlib.Map`. The pre-existing checked `update keys` workloads continue to
  cover replacement of every existing integer and string binding.
- The source `Some changed` signal increases allocation for successful
  removals; `patricia-bench.md` records the measured tradeoff and leaves a
  physical-child-identity extraction refinement for later evaluation.
- **2026-08-29 — fused generic-combine leaf cases**: added checked leaf/tree
  and tree/leaf workloads whose one-sided bindings are transformed and whose
  overlapping binding is deleted. `make proof`, `make`, the randomized oracle,
  and `make benchmark` passed.
- Source-level integer and string workers now fuse overlapping replacement
  into `map_filter`; their lookup and `wf` laws are proved under
  `f None None = None`. At 10,000 bindings, allocation fell from 120,128 to
  120,027 words for integer cases and from 140,170 to 140,023 words for string
  cases. Single-run timings remained too noisy for a stronger conclusion.
- **2026-08-29 — bounded string prefix scanner**: added
  `agrees_before_from`, proved its exact prefix law and
  `agrees_before_bounded_eq`, and routed pure and native string combine/union
  through the bounded worker. `make proof`, `make`, the deterministic oracle,
  and `make benchmark` passed.
- The packed native scanner compares only complete bytes and the relevant
  high bits before the split. Four-character half-overlap union allocation
  fell from 40,330 to 128 words at 10,000 bindings and from 400,347 to 143
  words at 100,000 bindings. The checked single-run times were 0.051 ms and
  0.532 ms respectively; these timings are observations, not thresholds.
- **2026-08-29 — string merge prefix cases**: proved whole-branch prefix
  extraction, equal-split sample rebasing, deeper-root containment, and
  disjoint-root separation at the exact first differing bit. The disjoint
  result produces the `all_keys` hypotheses consumed directly by
  `join_separated_correct_wf`. `make proof`, `make`, the randomized oracle,
  and `make benchmark` passed.
