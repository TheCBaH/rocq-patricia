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
- **done**: prove `combine_fuel` lookup correctness and well-formedness.
- **done**: lift the result to public `combine` under
  `f None None = None`.
- **done**: derive left- and right-biased union laws.
- **done**: add string `beq` with pointwise and lookup-extensional correctness
  theorems.
- **done**: specify the prefix-free bit-lexicographic order and prove that
  direct-string `elements` is strongly sorted by it on well-formed trees.
- **done**: package lookup-based finite-map equivalence for both key variants,
  prove its equivalence-relation laws and exact correspondence with binding
  membership, and connect equality-reflecting `beq` to it.

## M4: Harden the public extracted API

- **done**: generate explicitly named internal modules and expose abstract map
  types through handwritten `PatriciaMap` and `StringPatriciaMap` interfaces;
  constructors, fuel/change workers, packed split tokens, and proof-internal
  helpers are absent from the supported API.
- **done**: expose an abstract `PatriciaMap.Key.t`, reject non-positive native
  integers in its only public constructors, and test both invalid inputs and
  the accepted `1` / `max_int` boundaries.
- **done**: replace the raw two-option public `combine` callback with explicit
  `left_only`, `right_only`, and `both` cases, making absence from both inputs
  unrepresentable and enforcing the finite-map contract at the wrapper boundary.
- **done**: retain a separately packed backend extracted directly from the Rocq
  definitions and compare it with the optimized backend during the normal build.

## M5: Reduce the trusted native-refinement boundary

- **in progress**: `NativeRefinement.v` formalizes the 62-bit positive-key
  domain and the logical-string-position/packed-token codec. Its kernel proofs
  cover decode-after-encode, valid tags, injectivity, ordering, and a safe
  source-level packed `bit_at` worker correct at encoded positions. They also
  prove the valid-token round trip and characterize the packed first difference
  as the unique unequal valid token after an equal prefix; the safe worker also
  rejects out-of-range byte reads and tags 9–15, while its marker is true
  exactly for an in-range byte. A safe structural bytewise scanner is proved
  equal to packed `first_diff`, including its first-differing-character-bit
  choice. Proving the handwritten OCaml primitive/string correspondence and
  XOR/leading-zeroes realization against that scanner is next.
- **done**: require every well-formed string branch's cached sample to be a
  resident binding and preserve that requirement through all smart operations.
- **later**: replace handwritten direct `set`, `combine`, and biased-union
  realizers with proved source-level workers or prove their refinements.
- **done**: discover every top-level proof declaration and run `Print Assumptions`
  for all of them during normal automated validation.

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
- **2026-08-29 — direct-string generic combine**: proved simultaneous lookup
  correctness and well-formedness for every sufficiently fuelled
  `combine_fuel`, covering equal roots, either containment direction, failed
  prefix agreement, filtered empty sides, and leaf fusion. Lifted the result
  to public `combine` under `f None None = None`; `make proof`, `make`, the
  randomized oracle, and `make benchmark` passed.
- **2026-08-29 — direct-string biased unions**: derived left- and right-biased
  lookup and well-formedness laws from the generic `combine` theorem. Rocq
  reports both exported theorems closed under the global context; `make proof`,
  `make`, the randomized oracle, and `make benchmark` passed.
- **2026-08-29 — direct-string extensional equality**: added and exported
  `beq`, proved its pointwise Boolean law and equivalence to equality of every
  lookup under an equality-reflecting value comparator, and added randomized
  checks over differently rebuilt trees. Rocq reports both theorems closed
  under the global context; `make proof`, `make`, the randomized oracle, and
  `make benchmark` passed.
- **2026-08-29 — direct-string element ordering**: defined `bit_lex_lt` by
  the first differing prefix-free logical bit and proved
  `wf_elements_bit_lex_sorted`, which relates every earlier key to every later
  key. Added randomized byte-lexicographic ordering checks over empty,
  prefix-related, NUL-containing, non-ASCII, and arbitrary-byte keys.
- **2026-08-29 — finite-map extensionality**: packaged lookup equality as
  `equiv` for both key variants, proved reflexivity, symmetry, transitivity,
  and equivalence to identical binding membership in `elements` on
  well-formed trees. Equality-reflecting `beq` is proved equivalent to this
  relation; structural equality is deliberately not claimed. `make proof`,
  `make`, the randomized oracle, and `make benchmark` passed, and Rocq reports
  the exported extensionality theorems closed under the global context.
- **2026-08-29 — abstract extracted API**: the build now renames generated map
  backends to `PatriciaInternal` and `StringPatriciaInternal` and compiles
  handwritten wrappers whose `.mli` files keep both map types abstract. Public
  signatures contain only proved smart operations; constructors, routing
  metadata, packed positions, and proof-internal workers remain internal. The
  oracle adds wrapper-level functional checks, and the native benchmark now
  uses only the abstract interfaces. `make` and `make benchmark` passed.
- **2026-08-29 — checked native integer keys**: `PatriciaMap.Key.t` is abstract
  and can be created publicly only by `of_int` or `of_int_exn`, both of which
  reject zero and negative integers. Tests cover `min_int`, `-1`, zero, one,
  and `max_int`; wrapper operations and the native benchmark now consume the
  validated type. The representation remains an allocation-free native `int`.
  `make`, the randomized oracle, and `make benchmark` passed.
- **2026-08-29 — enforced public combine contract**: both abstract wrappers now
  accept a `combiner` record with `left_only`, `right_only`, and `both`
  callbacks. The wrappers map the raw absent/absent case directly to absence,
  so supported callers cannot violate `f None None = None`. Wrapper tests cover
  all three callbacks, including overlap deletion; `make`, the randomized
  oracle, and `make benchmark` passed.
- **2026-08-29 — proof-aligned differential backend**:
  `PatriciaReferenceExtract.v` generates the executable Rocq definitions with
  no Patricia-specific custom realizers, and the build packs the result under
  `PatriciaReference` so it can coexist with the optimized modules. The normal
  build compares updates, removals, maps, filtering, combine, both unions,
  folds, equality, lookup/membership, and logical-versus-packed string bit
  operations across the two backends. `make`, both deterministic test suites,
  `make benchmark`, and `git diff --check` passed.
- **2026-08-29 — exhaustive assumption audit**: the normal build now discovers
  every top-level `Lemma`, `Theorem`, and `Corollary` in the two bit modules and
  two map-proof modules, runs `Print Assumptions` for each, and fails on axioms,
  Rocq errors, anomalies, or a declaration/result count mismatch. All
  then-current declarations were closed under the global context; `make`, both
  deterministic test suites, `make benchmark`, and `git diff --check` passed.
- **2026-08-29 — cached-sample residency invariant**: `wf_branch` now carries
  `resident sample (Branch ...)`, defined as a successful lookup of the cached
  key. Smart branch collapse, mapping/filtering, removal, existing and fresh
  insertion, join, generic combine, and both unions all preserve the stronger
  invariant. `wf_cached_sample_resident` exports the consequence directly. All
  209 proof declarations are closed under the global context; `make`, both
  deterministic test suites, `make benchmark`, and `git diff --check` passed.
- **2026-08-29 — representation-relation foundation**: added
  `NativeRefinement.v`, which specifies the 62-bit native positive-key domain
  and the logical-position to packed-token codec used by string extraction.
  Its initial 13 closed lemmas proved codec validity, decoding, injectivity,
  order, and semantic transport. The next two lemmas add a safe source-level
  packed `bit_at` worker and prove it agrees with the logical bit view at every
  encoded position. The normal proof target and source-driven assumption audit
  include this module; the current `make` passed with 224 declarations closed
  under the global context and both deterministic test suites passing. The
  OCaml realizer refinements are deliberately still pending.
- **2026-08-29 — deterministic direct-string merge shapes**: added fixtures
  that inspect the packed-root dispatch relation and require each of equal
  roots, left containment, right containment, and disjoint prefixes. Every
  fixture checks normal and filtering `combine`, `union_left`, and
  `union_right` against the reference map. This closes the previously missing
  merge-shape validation item; it is test coverage, not a refinement proof of
  the handwritten native merge.
- **2026-08-29 — canonical packed first difference**: proved that any unequal
  logical bit preceded by an equal logical prefix is exactly `first_diff`, and
  transported the result to the safe packed `bit_at` worker at encoded tokens.
  This records the prefix-loop invariant required by a future bytewise scan;
  it does not yet verify the handwritten native string access or scan.
- **2026-08-29 — safe bytewise first-difference scanner**: defined a structural
  byte-at-a-time scanner, with a bounded eight-bit worker for a mismatching
  character, and proved it equal to `packed_first_diff`. This closes the
  source-level scan equivalence; correspondence to OCaml unsafe reads and its
  XOR/leading-zeroes implementation remains a target-language obligation.
- **2026-08-29 — exact packed-token specification**: proved that decoding then
  re-encoding any valid packed token is identity, and used this to state both
  directions of `packed_first_diff` directly over native tokens: its result is
  valid, differs at that token, and agrees at every earlier encoded position.
  The theorem rules out invalid tag results but is not yet a bytewise-scan
  refinement.
- **2026-08-29 — safe packed-read guards**: proved the safe source-level
  packed `bit_at` worker returns `false` after the final byte and for every
  invalid tag (9–15). This models the checks surrounding native unsafe access;
  proving their correspondence to that primitive remains open.
- **2026-08-29 — packed-token guard validation**: the native oracle now checks
  all sixteen tags for in-range and out-of-range byte indices on empty,
  NUL-containing, high-byte, and long-prefix inputs, and rejects any
  `first_diff` result with an invalid tag. This is focused executable evidence
  for the packed guard contract, not a refinement proof.
- **2026-08-29 — exact packed continuation marker**: proved that the safe
  packed worker returns `true` at tag zero exactly when the indexed byte exists,
  using companion in-bounds and past-end `String.get` laws. This completes the
  safe model of the native byte-presence guard, but not unsafe-access refinement.
