# Verified native string primitives: implementation plan

Date: 2026-09-11. Status: proposed; no replacement or new performance result
is claimed by this document.

## Objective and ownership

Replace the handwritten implementations of `StringBits.bit_at`,
`StringBits.first_diff`, and `StringBits.agrees_before_bounded` with proved
executable workers, without reproducible performance regressions on the
acceptance workloads. Preserve native byte strings, packed split tokens,
indexed access, traversal behavior and allocation characteristics.

The actionable tracker is [patricia-str-tood.md](patricia-str-tood.md).
This plan specializes S1/S2 and I2–I4 of
[patricia-native-verification.md](patricia-native-verification.md).
That document retains ownership of the overall native inventory and V2
milestones; the new tracker owns the detailed string-worker tasks. Closing a
local task does not automatically close its parent native-verification item.
[patricia-todo.md](patricia-todo.md) owns project-wide decisions, especially
D2's logical public model and D5's empirical performance boundary.
[SPECIFICATION.md](SPECIFICATION.md) remains authoritative for public claims.
Historical performance evidence is in [patricia-str.md](patricia-str.md) and
[patricia-bench.md](patricia-bench.md).

## Recommended approach

Introduce a separate executable string-bit implementation layer over a small
native primitive interface. Prove its workers against the existing logical
models, then extract their control flow normally. Use explicit recursion on
accessibility proofs in `Prop` for the indexed loops, following the successful
union workers in [StringPatriciaUnion.v](StringPatriciaUnion.v).

Do not extract the proof byte arrays as runtime lists or recursively destruct
logical strings in a hot scanner. The existing structural first-difference
extraction experiment copied a suffix at each step through `String.sub`; its
source also wraps recursive results with `option_map`. Replacing byte access
alone would not establish tail recursion or eliminate repeated result
allocation. See the V2.5 evidence in the parent tracker.

### Primitive interface and remaining trust

Expose native length, guarded byte-code access, integer comparisons,
increment, shifts, XOR, AND, OR, and string physical equality. Specify:

- Length and indexed byte codes agree with the logical string representation.
- An unsafe read is used only at a nonnegative index strictly below length.
- Byte codes lie in `0 .. 255`.
- Native arithmetic agrees with the mathematical operation under proved
  operand, result and shift-count bounds.
- A successful string identity test implies equal logical byte strings;
  failure makes no claim.

Bounds, representation evidence and termination evidence must erase. Specialize
the primitive interface before execution; do not pass a record of callbacks
through every recursive call. Inspect generated code to establish that the
chosen extraction arrangement achieves this.

The first milestone removes handwritten algorithm bodies, retaining explicit
primitive contracts and ordinary extraction/compiler/runtime assumptions.
It does not prove OCaml primitive execution or end-to-end compilation. Moving
a complete scanner into a new primitive or unchecked postprocessor does not
discharge its algorithmic obligation.

## Worker designs and proof obligations

| Worker | Existing foundation in `NativeRefinement.v` | Proposed executable shape |
| --- | --- | --- |
| `bit_at` | `native_packed_bit_at_refines_representation` and codec/access laws | Constant-time shifts, masks and one guarded byte read |
| `first_diff` | `native_string_first_diff_refines`, byte XOR laws and `native_string_first_diff_with_identity_refines` | Indexed tail recursion, nonzero-XOR mask scan and one final packed result |
| `agrees_before_bounded` | `native_bounded_prefix_scan_correct` and `native_terminal_mask_equal_correct` | Closed Boolean byte loop with erased termination proof |

### Packed bit access

Decode `byte = token lsr 4` and `tag = token land 15`. Check presence before
reading; tag 0 denotes the continuation marker, tags 1–8 select a data bit,
and tags 9–15 retain the current false result. Prove the native shift-and-mask
test agrees with `native_code_bit`, then compose the existing representation
theorem. Preserve the current guard order and avoid added allocation.

Logical and native positions must be related, not identified:
`9 * byte + tag` corresponds to `16 * byte + tag` for `tag < 9`.
The replacement theorem must compare operations through this codec.

### Indexed first difference

Keep the successful physical-equality early return. Otherwise cache lengths
and their minimum, scan by index, and compute each byte XOR once. At the
common-length sentinel, return `None` for equal lengths or the shorter
string's continuation-marker token. On a nonzero XOR, find its first set bit
from the most significant end and construct the absolute token once.

The outer invariant is `byte <= common` and equality of all preceding bytes.
Use `common - byte` as the decreasing measure in an erased accessibility
proof. Prove equivalence to the existing structural first-difference model
without executing that model's suffix traversal or `option_map` chain.

The inner invariant includes `0 < difference < 256`,
`mask = 128 >> count`, and zero higher bits at previously examined positions.
It must establish a set bit is reached within eight tests, all shifts are
valid, and the result tag lies in 1–8. Return an integer from this worker;
nonzero input removes any need for an internal optional result. Keep
termination proof data out of its runtime arguments.

Preserve constant stack usage, the same-object shortcut and no allocation
proportional to scanned prefix length. Measure fixed closure and result
allocation rather than assuming the current first-difference body allocates
only its final `Some`.

### Bounded prefix comparison

Retain the current branch order:

1. At the split byte, evaluate the terminal tag.
2. Otherwise, at the common-length sentinel, compare lengths.
3. Otherwise, compare complete bytes and advance on equality.

At tag 0 the continuation marker is excluded. At tag 1 only that marker is
included; at tag `t` the terminal data comparison covers the high `t - 1`
bits. Preserve the mask `(255 lsl (9 - tag)) land 255` for valid nonzero tags,
and reuse `native_terminal_mask_equal_correct`.

Use the invariant `byte <= min(split_byte, common)` and an erased measure
`min(split_byte, common) - byte`. Relate the worker to the existing
sufficiently fuelled scan. Discharge unsafe-read bounds from the invariant;
do not inherit redundant list-model presence checks in the complete-byte
path. Pass state as separate, fully applied arguments, preserving the closed
loop rather than allocating state tuples or capturing recursive closures.

The result must remain Boolean. Computing `first_diff` and discarding its
option reintroduces the allocation that motivated this primitive.

### Range closure

Reuse the existing conditional packed-capacity, byte-index and successor
lemmas. The retained end-inclusive capacity condition is
`16 * length + 8 < 2^62`. Audit every executable intermediate, including
token construction and mask shifts. Connecting runtime string lengths and
allocation limits to this condition remains a separate obligation; do not
claim the conditional source lemmas prove it. Logical codec conversions used
only in proofs should not become runtime arithmetic.

## Integration and representation relation

The current extraction changes logical positions into packed tokens without
an explicit executable split type. Therefore removing three directives alone
does not establish map-level refinement.

An incremental candidate may redirect the existing bindings to generated,
proved native workers. Record the remaining binding and representation
correspondence as trusted; do not describe an alias as ordinary extraction of
the original logical function. Ensure no handwritten worker body remains in
that binding.

For a stronger source integration, investigate parameterizing executable map
consumers over the bit operations and split representation, instantiating with
the native layer and proving the map representation relation. Establish the
scope and code shape before committing to this broader refactoring. Preserve
the logical API and avoid runtime packing/unpacking at each routing step.

Retain the reference extraction and wrapper abstraction. Audit generated
dependencies for substring copying, runtime list conversion, recursive
arithmetic, module-name shadowing, and unintended logical helper calls.

## Alternatives

Explicit accessibility recursion is described by Xavier Leroy in
[Well-founded recursion done right](https://xavierleroy.org/publi/wf-recursion.pdf).
Its suitability here is supported by the repository's union extraction result,
but each new worker still needs its own code and performance checks.

Primitive `PString` is an experiment, not the default: the installed runtime
limits strings to 16,777,211 bytes and its `get` performs index conversion and
checks. Adopting it directly would require resolving the supported-domain and
access-cost differences. Importing primitive strings or integers alone does
not prove the OCaml foreign interface.

If ordinary extraction cannot preserve performance, investigate verification
of the existing OCaml bodies. [CFML](https://github.com/charguer/cfml) documents
testing with Coq 8.20 and OCaml below 5; compatibility with this Rocq 9.2
development and the exact primitive semantics must be established.
[Verified extraction to Malfunction](https://github.com/MetaRocq/rocq-verified-extraction)
addresses part of the extraction boundary, retains downstream compiler/FFI
obligations, and documents some optimizations as unverified. Neither alternative
is an already validated replacement for these workers.

## Acceptance and implementation order

Implement `bit_at`, then bounded prefix comparison, then `first_diff`.
Build each candidate alongside the current implementation before selection.

Correctness requires closed refinement theorems, explicit assumptions,
reachable range/access bounds, and the existing exhaustive, structural and
differential tests. Inspect OCaml and compiler output for tail calls, fully
applied recursion, fuel, closures, copying and intermediate results.

Measure baseline and candidate on the same compiler and machine with repeated,
interleaved runs. Establish noise before judging elapsed-time medians and
dispersion; record allocated words separately. No reproducible regression
outside baseline variability is acceptable. Equal asymptotic complexity or
matching allocation alone does not establish equal performance.

Include primitive workloads for empty strings, binary bytes, every valid tag,
bit-access invalid tags, proper prefixes, early/late differences, same-object
strings, separately allocated equal strings and increasing common-prefix
lengths. Use batches large enough to measure short operations reliably.

Also measure map build, lookup, membership, existing/fresh update, removal,
combine and both union biases at 10K and 100K, then larger sizes as practical.
Include disjoint, overlapping, subset and equal maps, separately built equal
maps, and long-prefix keys. Retain the existing near-zero-allocation union
cases. Record new measurements in `patricia-bench.md` with commands and
toolchain details before selecting a public replacement.

Formal cost and GC semantics remain the separate N4 expansion. This plan's
performance gate is empirical, not a universal no-slowdown theorem.
