# Patricia public specification

Status: current custom API; native-boundary clarification updated 2026-09-09.

This document fixes the verified claim for the abstract OCaml interfaces
[`PatriciaMap.mli`](PatriciaMap.mli) and
[`StringPatriciaMap.mli`](StringPatriciaMap.mli). The kernel-checked results
apply to the corresponding pure Rocq definitions. Extraction and the optimized
OCaml backend have the separate trust status stated below.
The implementation inventory and separate gap-closing tracker are in
[`patricia-native-verification.md`](patricia-native-verification.md). Proposed
strategies do not change the contracts or proof claims in this specification.

## Claim and domains

The claim is functional correctness of the pure finite-map models: public
operations preserve their representation invariant and obey the pointwise
lookup laws in the theorem checklist. The optimized backend is tested against
both independent finite-map oracles and a proof-aligned extracted backend; it
is not an end-to-end proved refinement.

`PatriciaMap` is proved over unbounded Rocq `positive` keys. Its supported
64-bit OCaml implementation domain is `1 .. max_int`, equivalently
`1 .. 2^62 - 1`. `PatriciaMap.Key.of_int` and `of_int_exn` reject zero and
negative inputs, and the abstract `Key.t` prevents unsupported integers from
reaching map operations through the public interface.

`StringPatriciaMap` is proved over logical Rocq strings and supports arbitrary
OCaml byte strings, including the empty string, embedded NUL, and non-ASCII
bytes. Keys are byte sequences; no text encoding, Unicode normalization, or
locale-sensitive comparison is implied.

Map values are unrestricted. Laws for `beq eq_value` require
`eq_value x y = true` exactly when `x = y`.

## Invariant boundary

The public map types are abstract. Clients can construct maps only with
`empty`, `singleton`, and invariant-preserving operations. Tree constructors,
branch metadata, cached string samples, packed positions, fuel arguments, and
internal workers are not supported interfaces.

The positive-key invariant requires non-empty children and correct common
prefix and routing-bit metadata. The string invariant additionally requires
strictly increasing descendant split positions, correct prefix/routing bits,
and a cached branch sample that is a resident binding. Every map returned by a
public constructor or transformer satisfies the corresponding pure invariant,
assuming its map inputs do.

Public `combine` exposes only `left_only`, `right_only`, and `both`. Absence
from both inputs is fixed to `None` by the wrapper, enforcing the source
theorem's `f None None = None` premise.

## Operation semantics

For a key `k`, write `lookup k m` for `get k m`. Each statement is pointwise;
maps with the same lookup result at every key are observationally equal even
if their trees or physical identities differ.

| Operation | Contract |
| --- | --- |
| `empty` | `lookup k empty = None`. |
| `is_empty` | True exactly for the empty public map. |
| `singleton k v` | Maps `k` to `v` and every other key to `None`. |
| `get k m` | Returns the binding at `k`, if one exists. |
| `mem k m` | True exactly when `get k m` is `Some _`. |
| `set k v m` | Returns `Some v` at `k` and preserves every other lookup. |
| `remove k m` | Returns `None` at `k` and preserves every other lookup. Removing an absent key returns the identical pure tree; the wrapper tests also check native root identity. |
| `of_list bindings` | Bulk-loads bindings. At `k`, returns the value in the first binding for `k`, if any, otherwise `None`. |
| `map f m` | Preserves keys and changes `Some v` at `k` to `Some (f k v)`. |
| `map_filter f m` | Changes `Some v` at `k` to `f k v`; absent keys remain absent. |
| `combine f left right` | Uses `left_only`, `right_only`, or `both` according to the two lookups. A returned `None` omits the key. |
| `union_left left right` | Uses the left binding when present, otherwise the right binding. |
| `union_right left right` | Uses the right binding when present, otherwise the left binding. |
| `elements m` | Contains each represented binding exactly once and no other binding. |
| `fold f m init` | Equals `List.fold_left (fun state (k,v) -> f state k v) init (elements m)`. |
| `beq eq_value left right` | True exactly when both maps have identical lookup results, provided `eq_value` reflects value equality. |

Callback invocation counts, callback order for operations other than `fold`,
exception behavior inside user callbacks, and physical identity are not part of
the verified functional contract.

## Traversal order

Both `elements` implementations visit a branch's left (`false` routing bit)
subtree before its right (`true` routing bit) subtree. `fold` processes exactly
that list order, from its supplied initial state.

For positive keys, no theorem currently identifies this traversal with
increasing `Pos.compare`, so numeric sortedness is not part of the verified
public contract.

For logical strings, `StringPatriciaProof.wf_elements_bit_lex_sorted` proves
strong ordering by the prefix-free bit view: each byte has a `true`
continuation marker followed by its bits most-significant first, and the end
marker is `false`. The bridge from this logical relation and packed native
positions to OCaml `String.compare` remains outside the proof claim. Therefore
the current API does not advertise `elements` as standard-library `bindings`.

## Theorem checklist

The normal assumption audit checks every listed theorem, along with all other
project lemmas, is closed under the global context.

| Public obligation | Positive-key proof | Direct-string proof |
| --- | --- | --- |
| Empty/singleton lookup and well-formedness | `get_empty`, `get_singleton_same`, `get_singleton_other`, `wf_empty_ok`, `wf_singleton_ok` | `get_empty`, `get_singleton_same`, `get_singleton_other`; `wf_empty` and `wf_leaf` constructors |
| Membership and emptiness | `mem_spec`, `is_empty_spec` | `mem_spec`, `is_empty_spec` |
| `set` law and invariant | `set_correct_wf` | `set_correct_wf` |
| `of_list` law and invariant | `of_list_correct_wf` | `of_list_correct_wf` |
| `remove` law, invariant, and absent identity | `remove_correct_wf`, `remove_absent_identity` | `get_remove`, `remove_wf`, `remove_absent_identity` |
| `map` law and invariant | `get_map`, `map_wf` | `get_map`, `map_wf` |
| `map_filter` law and invariant | `map_filter_correct_wf` | `get_map_filter_wf`, `map_filter_wf` |
| `combine` law and invariant | `combine_correct_wf` | `combine_correct_wf` |
| Biased-union laws and invariants | `union_left_correct_wf`, `union_right_correct_wf` | `union_left_correct_wf`, `union_right_correct_wf` |
| Binding membership and unique keys | `elements_spec_wf`, `elements_keys_nodup_wf` | `wf_elements_spec`, `wf_elements_keys_nodup` |
| Traversal/fold agreement | `fold_elements` | `fold_elements`, `wf_elements_bit_lex_sorted` |
| Extensional equality | `beq_extensional_wf`, `equiv_elements_wf` | `beq_extensional_wf`, `equiv_elements_wf` |
| Public combine fuel is sufficient | `public_combine_fuel_sufficient` | `public_combine_fuel_sufficient` |

The theorem names in the middle column are in
[`PatriciaProof.v`](PatriciaProof.v); those in the last column are in
[`StringPatriciaProof.v`](StringPatriciaProof.v).

## Trusted computing base

For the pure theorem claim, the trusted base is the Rocq kernel and the Rocq
standard library used by the development. `make assumptions` scans all source
theorem declarations and asks Rocq to print their assumptions; it rejects
project axioms or unresolved assumptions. This audit does not inspect
extraction directives.

Executing the supported native library additionally trusts:

- Rocq's OCaml extraction mechanism and the generated-code boundary;
- the OCaml compiler, runtime, native integer operations, byte-string
  primitives, and the host platform;
- the standard `positive`, `N`, `nat`, and native-string extraction mappings;
- the handwritten wrapper modules that enforce abstract maps, positive native
  keys, and the restricted combine callback;
- integer realizer code for equality/order tests, shifts, masks, prefixes,
  routing bits, and highest-differing-bit selection;
- the source-extracted biased-union workers' target physical-equality contract:
  when `changed == original` succeeds, both references denote the same
  current tree object and hence have identical `get` results at every key.
  This is exactly the positive-direction `native_same_sound` premise used by
  the source refinement; it neither requires recognizing all equal maps nor
  proves retained sharing or allocation behavior. It is a runtime/compiler
  representation contract, not a portable consequence of OCaml `==`: for
  non-mutable values the documented language guarantee is only `compare = 0`,
  which is too weak for arbitrary (potentially mutable) map payloads;
  `NativeHeapRefinement.v` now models the required bridge with immediate empty
  values, allocated heap roots, and abstract current heap locations. Its
  object layer pairs each current OCaml root with its source-tree
  interpretation, permits distinct locations for equal source trees, and
  proves that a per-call `(==)` adequacy theorem discharges both source
  `native_same_sound` premises. A whole-worker target simulation must relate
  actual recursive execution, each current tree object and each `(==)` result
  to that model; the abstract bridge alone does not provide it. The
  [OCaml 4.14 library reference](https://ocaml.org/releases/4.14/ocaml-4.14-refman.pdf)
  specifies physical equality but does not supply this compiler/heap
  refinement theorem. `make ocaml-physical-equality-audit` additionally
  source-checks the selected 4.14.3 implementation path from `Stdlib.(==)`
  through `%eq`, `Pintcomp Ceq`, `cmmgen`, and `Ccmpi` to native word
  comparison; this is pinned implementation evidence, not a proof about the
  compiler binary or runtime. `make native-union-realizer-audit` checks that
  the generated source workers remain direct `Acc` recursion with no runtime
  size/fuel argument or nested recursive closure; it remains a syntactic
  audit rather than a refinement proof.
  The bytecode and native union oracles additionally require distinct
  allocated leaf and branch roots containing distinct mutable payload objects
  to fail `(==)` under the pinned runtime; this is targeted finite evidence
  against a structural-equality lowering, not a portable heap theorem. They
  also retain aliased branch roots across a major collection and compaction,
  then require both no-op biased unions to reuse that root.  In addition, the
  left-biased oracle compacts four-binding integer and direct-string roots
  before exercising its equal-header and all four containment-child reuse
  routes. This is finite evidence for the selected moving-GC runtime, not a
  heap theorem;
- packed string positions, native `bit_at`, bytewise first difference,
  bounded prefix comparison, `Char.code`, integer XOR/leading-zeroes, and
  guarded `String.unsafe_get` calls;
- cached string representatives and specialized string biased unions.

Both general `combine` definitions are extracted directly from the proved
fuel-free structural workers; as usual, this still trusts ordinary extraction
and the OCaml compiler rather than proving compilation correctness.
Public string `set` likewise extracts the proved two-descent worker.
Public string `map_filter` selects the separately proved cache-aware traversal:
on well-formed inputs its smart branches read a resident cached sample rather
than structurally descending after a child filter has collapsed.
Public string `remove` likewise selects a separately proved cache-aware worker;
an absent key returns the exact input root, while changed branches use resident
cached samples.
The public string `combine` uses cached smart branches and cached joins; their
conditional refinements preserve its existing lookup and well-formedness
contract.
The former extraction-only string representative is gone: the total structural
source definition remains only for raw-tree proofs, while executable public
paths use proved cached consumers.

The native bounded-prefix byte loop has a source-level byte-scan model:
`native_bounded_prefix_scan` follows its complete-byte, shorter-length
sentinel and terminal partial-code branches, while its guarded-access lemmas
make the model's unsafe reads explicit. `agrees_before_bounded_eq` still
concerns only the logical bit-scanning specification: a theorem connecting the
byte scan to it, its minimum-length invariant, and the target XOR/mask loop
remain open. The structural first-difference model likewise leaves the indexed
OCaml scan, shifting-mask loop and identity shortcut to be connected. These
algorithmic obligations
are separate from the standard primitive contracts in the audit below.

`NativeRefinement.v` proves part of the representation-level source model,
including the packed-position codec and safe first-difference model. It does
not remove the native primitives or handwritten algorithms above from the
trusted boundary. The proof-aligned reference extraction shares the standard
numeric/string mappings and extraction/compiler boundary, but omits the
Patricia-specific algorithm realizers.

### Standard extraction-mapping audit

Both extraction units import the following Rocq standard mapping modules. They
are runtime realizers, not kernel-checked refinement proofs; the reference
backend shares them deliberately, so differential testing does not validate
this row of the trust boundary.

| Source representation | Mapping module and native representation | Remaining foreign obligation |
| --- | --- | --- |
| `positive`, `N`, `Z` | `ExtrOcamlZInt`: OCaml `int`, including constructor eliminators and native arithmetic/comparison realizers | Values and every intermediate arithmetic result must remain in the intended finite range. The supported wrapper only accepts positive keys through `max_int`; masks and temporary arithmetic remain subject to the 62-bit model and the OCaml-operator contract. |
| `nat` | `ExtrOcamlNatInt`: OCaml non-negative `int`, with native successor, arithmetic, comparison, and division realizers | Bounds are required for string lengths, logical positions, fuel, and traversal counters; overflow is not represented by the source model. |
| `Ascii.ascii`, `Byte.byte`, `string` | `ExtrOcamlNativeString`/`ExtrOcamlChar`: OCaml `char` and byte string, with constructor elimination through `String.length`, `String.get`, and `String.sub` | `NativeRefinement.v` fixes the source model as the `Ascii.N_of_ascii` byte-code array and proves its length/access laws, byte bound, and guarded packed-bit refinement. The remaining FFI contract is that `String.length` returns that array length, `Char.code (String.unsafe_get s i)` returns its code for `i < length`, and OCaml short-circuit evaluation does not evaluate an `unsafe_get` before the proved guard succeeds. |
| Reference-only `String.length` | Explicit inline mapping to `Stdlib.String.length` in `PatriciaReferenceExtract.v` | This removes a generated shadowing `String` unit but remains part of the shared native-string boundary. |

The optimized extraction then adds the Patricia-specific realizers enumerated
in `PatriciaExtract.v`; those are separately listed in the trusted computing
base above. No `Axiom`, `Admitted`, or extraction directive turns any of these
runtime mappings into a theorem about OCaml execution.

## Validation and exclusions

`make` compiles the Rocq proofs, performs the source-driven assumption audit,
regenerates both extraction backends, compiles the abstract wrappers, runs the
deterministic randomized structural/oracle suite, and runs optimized-versus-
reference differential tests. Repository CI runs this complete gate from a
fresh checkout.

`make benchmark-smoke` runs a small checked benchmark workload in CI. It is a
functional smoke test only. `make benchmark` remains the local measurement
run; neither target imposes a machine-independent performance threshold.

The current claim excludes end-to-end native refinement, `Map.S`/`Set.S`
compatibility, standard-comparison traversal contracts, callback ordering
outside `fold`, asymptotic complexity, allocation bounds, and physical-sharing
guarantees. These require N1/N2, N3, or N4 in
[`patricia-todo.md`](patricia-todo.md), as applicable.
