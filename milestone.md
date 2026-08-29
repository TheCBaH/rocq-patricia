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
- **next**: add checked generic-`combine` workloads and fuse its leaf/tree
  mapping and replacement passes.

M1 completion requires `make`, the deterministic oracle test, and the native
benchmark to pass after each item.  Performance observations are evidence,
not machine-independent thresholds.

## M2: Remove the remaining string-union allocation hotspot

- **later**: define a bounded `agrees_before` scanner in `StringBits.v`.
- **later**: prove it equivalent to logical `agrees_before`.
- **later**: provide and validate the packed-token native realization without
  widening the undocumented extraction contract.
- **later**: rerun the 10K and 100K half-overlap allocation measurements and
  update `patricia-bench.md`.

## M3: Complete direct-string functional proofs

- **later**: prove the equal-split, containment, and disjoint-prefix lemmas
  needed by merge.
- **later**: prove `combine_fuel` lookup correctness and well-formedness.
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
