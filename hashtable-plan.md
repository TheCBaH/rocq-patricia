# Persistent generic hash table: implementation plan

Date: 2026-09-13. Status: implementation in progress; the tracker records the
current evidence and open gates.

The [design](hashtable-design.md) is the contract, [hashtable.md](hashtable.md)
is the original investigation, and [hashtable-todo.md](hashtable-todo.md) owns
progress. Some paths and Make targets below now exist; the tracker distinguishes
implemented evidence from remaining proposals. This work is
independent of the Patricia completion and native-verification trackers.

The [layout comparison](hashtable-design.md#hamt-versus-champ-runtime-and-proof-cost)
selects HAMT for lower initial proof effort. Evaluate any later CHAMP proposal
against the array HAMT, keeping hash and container choices comparable. CHAMP
requires additional data/child migration and normalization proofs; published
JVM gains are not an OCaml acceptance result.

## Delivery sequence

### H0 — Contracts and build skeleton

Create `HashTableSpec.v` with key equivalence, equality reflection and hash
congruence parameters, abstract lookup laws modulo equivalence, and integer,
byte-string and record/custom-equivalence instances. Specify `HashMap.Make` and
prove raw-hash normalization to 30 bits, including negative hashes. Fix depth
six, five-bit chunks, explicit seeds,
first-wins bulk loading and unspecified element order as in the design.
Record the toolchain versions actually used. Establish separate generation
paths `hashtable_reference_extracted/` and `hashtable_extracted/` to avoid
Patricia module collisions.

Prototype recursive node definitions and terminating join/update workers before
committing to the native container abstraction. Check which arguments survive
extraction. Choose a strictly positive source shape and record how later array
workers will relate to it. This prototype must not depend on unchecked axioms.

Exit: interfaces compile, contracts are explicit parameters, representation and
termination approach is demonstrated, and future build dependencies are mapped.

### H1 — Words, bitmap indexing and collision buckets

Implement `HashTableBits.v` and `HashTableBucket.v` with their lemmas. Cover
30-bit hash reconstruction, six-level divergence, 32-bit bitmap operations,
rank and dense-list edits. Prove bucket lookup/update/remove and normalization.
Keep bitmap width separate from hash width in every native range argument.

Exit: all primitive contracts compile and assumptions are audited, including
slot 31, full bitmap, empty insertion and equal-full-hash distinct keys.

### H2 — Executable source map and core proofs

Implement `HashTable.v`: raw nodes, independent flattened bindings, depth/prefix
invariant, join, lookup, set and remove. Put map theorems in `HashTableProof.v`.
Prove join first, then lookup, then update/removal with invariant preservation.
Establish unreachable fuel fallback and the six-branch height bound.

Exit: pointwise set/remove laws, collision uniqueness, routing and seed
preservation are kernel-checked with no admitted obligations. Existing Patricia
proofs still build.

### H3 — Complete API and reference OCaml release

Implement derived operations and their proofs, then
`HashTableReferenceExtract.v`. Add a pure executable test hash and a native hash
adapter whose trust is documented. Package the reference under a distinct
`HashTableReference` name; compile `HashMap.ml` / `.mli` with a generic
`Make(Key)` functor initially against this backend. Add string, integer and
record examples through this public functor. Hide generated constructors and
per-operation raw-hash access from clients;
keep user-supplied equality/hashing available through the functor parameter.

Add `HashTableTest.ml` and `HashTableDifferentialTest.ml` with deterministic
operation histories checked against an equality-based association-list oracle
and comparator-compatible `Map.Make` instances. Test adversarial hashes through
the public functor, equivalent but structurally different keys, representative
retention, first-wins bulk loading, and negative/large raw hash normalization.
Use multiple simultaneous key modules to check that callbacks stay associated
with the correct instance. Audit that no polymorphic key equality is introduced.

Exit: a proved source map is exported as a usable OCaml library, with complete
API theorems, passing wrapper/oracle tests and an explicit extraction boundary.
This is a deliverable in its own right; do not label it the compact-array HAMT.

### H4 — Native compact arrays and refinement

Implement `HashTableNative.v` and `HashTableNativeProof.v` for source-defined
native workers and a representation relation. Prove persistent sequence view
laws and operation refinement. Add bounded scalar/popcount workers and the
native primitive inventory. Implement minimal OCaml array realizers in
`HashTablePrimitives.ml` and extraction bindings in `HashTableExtract.v`.

Keep every array update fresh and arrays private. Inspect generated code for
unintended list conversion, copied string suffixes, callback dispatch in hot
loops, and whole-operation overrides. Compile both backends in the same test
binary. Switch the public wrapper only after the native gate passes.

Exit: modeled native operations refine the source; every remaining OCaml foreign
obligation is listed; bytecode/native differential tests and retained-version
checks pass. A tested foreign array implementation is not described as a
kernel-checked OCaml heap proof. CHAMP remains a separate future project.

### H5 — Build integration, evaluation and release record

Add the targets below, cleanup rules and CI integration using the current
Patricia workflow as a pattern. Publish correctness-checked comparative
benchmarks and the final theorem/foreign-contract inventory. Update README and
public specification to describe the implemented API and exact proof boundary.
Record commands, dates and results in the tracker before closing gates.

Exit: a fresh build runs all correctness gates for both libraries, CI is
configured, benchmark smoke passes, and performance/verification claims match
the evidence. Hosted CI results are recorded separately from local results.

## Proof completion order

Status reconciliation: 2026-09-20. Finish H2.G, then H3.G before resuming
H4/H5 expansion. Preserve the existing native work and rebuild it when source
proof changes require it. No native-array theorem is needed to close H2 or H3.
The tracker owns completion status; the theorem names below are proposals unless
explicitly described as existing.

All semantic statements use the existing explicit contracts: equivalence `E`,
equality reflection, seed-hash congruence, `table_wf`, and normalized hash bounds
for the keys involved. Keep those hypotheses visible, quantify contracts rather
than introduce axioms, and preserve arbitrary payload types without comparing
values. For worker proofs retain the existing depth/prefix/fuel premises where
needed; for public corollaries discharge them at the seeded root.

### P1 — Preserve unrelated bindings (H2.4, H2.5)

Prove exact binding preservation outside the modified equivalence class:

```text
~ E stored key ->
  (In (stored, old) (bindings (set_tree ... key value t)) <->
   In (stored, old) (bindings t))
~ E stored key ->
  (In (stored, old) (bindings (remove_tree ... key t)) <->
   In (stored, old) (bindings t))
```

Use fuel induction and the independent flattened view. Reuse
`bindings_join_worker`, `bindings_normalize_collision`, dense-child binding
splits, and insertion/replacement/deletion lemmas. In recursive branch cases
preserve both sibling segments and apply induction to the selected child.
Removal must cover empty-child compaction and singleton-parent collapse.
Collision helpers must preserve the exact pair, including its value; the
existing `bucket_get_set_other` / `bucket_get_remove_other` give the corresponding
lookup facts if useful. Derive their equality symmetry/transitivity premises
from the existing equivalence/reflection contract.

The existing `bindings_set_tree_key_origin` only preserves a key's origin, not
its old value; `bindings_remove_tree_in` only gives one direction. Neither is
sufficient alone. Prove the binding helpers with the weakest practical premises;
do not generalize joins to branch subtrees, which `set_tree` does not join.

Acceptance: both directions for exact unrelated bindings, including recursive
branches, compile in `HashTableProof.v` without admitted obligations.

### P2 — Complete public pointwise laws (H2.4, H2.5)

Lift P1 through `get_binding_iff`, using existing `table_wf_set` /
`table_wf_remove`, seed preservation and equivalence transitivity. For a query
not equivalent to the modified key, characterize every `Some old` result in
both maps; handle `None` explicitly by excluding a `Some` result on either side.
Proposed public lemmas: `get_after_set_other` and `get_after_remove_other`.

Combine these with existing `get_after_set_equiv` / `get_after_remove_equiv`:

```text
get q (set k v m) = if eqb q k then Some v else get q m
get q (remove k m) = if eqb q k then None else get q m
```

Acceptance: the two complete equations under the ordinary valid-map contracts,
with no extra assumption that the query is present or has a different hash.
Distinct equivalence classes may share a hash. Update H2.4/H2.5 only when these
theorems, their commands and results are recorded.

### P3 — Close the source gate (H2.G)

Map every H2 exit requirement to an actual theorem: P2 pointwise laws, existing
validity/uniqueness/routing, seed preservation, join and operation no-fallback,
and `wf_branch_path_bound`. Run `make hashtable-proof hashtable-assumptions proof`;
the last target checks existing Patricia proofs. Check the audit's declaration
coverage, including nested/indented declarations, and explicitly enumerate any
required theorem it misses. The current script only matches declarations at
column zero: it skips nine indented lemmas in `HashTableProof.v` (including
`table_wf_empty` and `table_wf_singleton`) and six instance lemmas in
`HashTableSpec.v`. Extend discovery for section declarations and use qualified
names for module declarations; verify all 15 are audited. Record commands,
date, count and result, then close
H2.G. An assumption audit proves the checked declarations have no unexpected
assumptions; it does not prove that every required declaration exists.

### P4 — Representatives and arbitrary first-wins loading (H3.1)

First establish the resident-representative update law: if `(stored, old)` is in
a valid map and `E key stored`, setting `key` keeps the exact `stored` key and
changes its value. Also establish that an absent equivalence class receives the
supplied key as representative. Reuse leaf/bucket retention, join bindings and
recursive branch splits; combine with P1 for unrelated entries. Lookup laws
alone cannot distinguish equivalent representatives.

Define an independent left-to-right input scan returning the first matching
`(representative, value)` pair. Prove an accumulator theorem for `add_first`:
an existing class and its representative/value are retained; an absent class
receives its first input match. Induct on the input list with a general valid
accumulator, using P2, `add_first_cons`, and `add_first_table_wf`.
Specialize to `empty` for arbitrary `of_list` input.

Acceptance: bulk lookup equals the value projection of that input scan, and
enumeration contains exactly the selected first representatives and values,
modulo unspecified element order. Include the no-match case. Existing
`get_of_list_binding_iff` describes the output, not first occurrence in the
input; existing `of_list_first_wins_equiv` covers only two equivalent entries.

### P5 — Assemble the remaining API laws (H3.1)

Use P2/P4 to package general singleton lookup/membership and bulk membership.
Retain the already proved `mem_binding_iff`, `elements_keys_nodup`,
`is_empty_iff_get_none`, validity and seed laws instead of reproving them.
`table_extensional` and its equivalence proof already exist; add set/remove
congruence under pointwise equality, and equality of `mem`/`is_empty` observations.
For maps with different seeds, require appropriate hash bounds at both seeds;
do not infer seed equality or tree equality from extensional equality.

Acceptance: a compact inventory maps each design/API requirement to a theorem
and its explicit hypotheses. Do not add map/merge/fold or equality of traversal
order to this release's proof scope.

### P6 — Close the reference release (H3.3, H3.4, H3.G)

Inventory the reference extraction/compiler/runtime boundary, machine-integer
realizers and normalization, lawful/stable equality and hashing callbacks, and
immutable storage with shallow payload sharing. Link each obligation to the
wrapper/extractor or relevant audit; distinguish tests from universal proofs.

Map the existing reference tests to every row of the test matrix below. Record
file/case and bytecode/native coverage, add only missing cases, and report any
unsupported case explicitly. Include all routing depths, slot 31/full occupancy,
collision normalization, equivalent representatives, integer/string boundaries,
multiple callback instances, seeds, retained versions and function/ref values.

Run the reference subset from freshly regenerated output in a disposable clean
checkout of the candidate changes, using these existing targets:

```sh
make hashtable-proof hashtable-assumptions proof
make hashtable-reference
make hashtable-extraction-audit hashtable-reference-test \
  hashtable-wrapper-test hashtable-wrapper-test-native \
  hashtable-differential hashtable-test-native
```

Run regeneration before its consumers; avoid concurrent extraction targets
writing the same directory. Record exact results and the final theorem/foreign
inventory before closing H3.G. A full `make hashtable` is useful regression
evidence, but neither it nor future H4 work substitutes for the H2/H3 inventories.

## Proposed build and verification targets

| Target | Responsibility |
| --- | --- |
| `hashtable-proof` | Compile all source and refinement proofs in dependency order |
| `hashtable-assumptions` | Audit all public/helper theorems and reject unexpected axioms or admitted proofs |
| `hashtable-reference` | Extract and compile list reference, pure test hash and wrappers |
| `hashtable-native` | Extract and compile native backend with primitive adapters |
| `hashtable-extraction-audit` | Check allowed primitive realizers, source-derived map workers and generated interfaces |
| `hashtable-test` | Public API tests plus internal structural/collision oracle |
| `hashtable-differential` | Reference/native/standard-map histories, seeds and retained versions |
| `hashtable-test-native` | Exercise the same native-sensitive cases through `ocamlopt` |
| `hashtable-benchmark` | Checked performance and allocation comparison |
| `hashtable-benchmark-smoke` | Small checked workload without timing thresholds |
| `hashtable` | Aggregate proof, audit, extraction, compilation and correctness targets |

The existing `check-assumptions.sh` discovers top-level theorem declarations in
all local `.v` files. Integrate new `.vo` prerequisites with that discovery so
`make assumptions` cannot import an unbuilt module. Explicitly enumerate or
extend discovery for nested/module-qualified theorems. Preserve the existing
closed-global-context policy: generic contracts should be quantified in theorem
statements. Include any native contract assumptions visibly in the inventory;
do not silently whitelist global axioms to make the audit pass.

At H3, run the reference subset; at H4, add native gates; at H5, wire the full
aggregate into ordinary build/CI without breaking Patricia targets. Separate
extraction directories and module names must allow both backends and both
Patricia maps to link together. Clean/rebuild validation must regenerate output
from `.v` sources, rather than depend on checked-in or stale generated files.

## Test matrix and evidence

| Cases | Required observation |
| --- | --- |
| Empty, singleton, replace, missing remove | API laws and invariant preservation |
| Constant hash, many distinct keys | No lost bindings; unique bucket keys; all deletion normalization cases |
| First difference at depths 0 through 5 | Correct unary chains and ordered child insertion |
| Slot 31 and all 32 children | Correct rank, bounds, insertion and deletion at every dense position |
| Delete to unary, then insert again | Remaining child's implicit depth stays valid |
| Integers, tuples/records, empty/NUL/high-byte/long/prefix strings | Generic API and each instance's key identity |
| Case-insensitive or record-ID equality | Congruent hashes, class uniqueness, lookup congruence and retained representatives |
| Native int keys: min_int, max_int, zero, negatives | Full keys preserved independently of normalized hashes |
| Negative/large raw hashes; different key modules | Correct normalization and callback association |
| Duplicate/equivalent `of_list` input | First representative and first value win |
| Several seeds and branches from an old version | Independent routing; unchanged retained bindings |
| Mutable references and functions as values | No payload comparison; shallow sharing contract |
| Random deterministic operation histories | Every current and sampled retained version agrees with the oracle |

Proof compilation establishes universal source/model properties. Runtime tests
establish finite target evidence. Benchmark measurements establish workload-
and machine-specific performance only. Keep these evidence types separate in
release notes and tracker entries.

## Risks and handling

Resolve nested recursion/container positivity in H0 before writing large proofs.
Prevent depth bugs by retaining unary branches and proving join prefix laws.
Prevent machine overflow by checking all bitmap intermediates, not just hashes.
Prevent false confidence from shared hash adapters by adding pure and controlled
hash instances. Prevent persistence violations with private storage, modeled
copy contracts and old-root tests. If native performance disappoints, preserve
the H3 reference release and report the result; do not replace source-defined
algorithms with unaudited extraction bodies to meet a timing target.
