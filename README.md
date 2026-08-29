# Standalone Patricia-tree sketch

This directory is intentionally independent of CompCert's `Maps.PTree` and
build.  It contains two compressed Patricia-tree sketches:

- `Patricia.v`: big-endian Patricia trees proved over unbounded positive keys
  and extracted as a native OCaml `int`-key API.
- `StringPatricia.v`: direct Patricia trees over byte strings. Branches store
  differing-bit positions; lookups route to one leaf and compare the key once.
  Strings are not converted to integers.

Run:

```sh
make -C patricia
```

`PatriciaBits.v` fixes the proof-side positive-key convention. `StringBits.v`
defines the prefix-free string bit view (a continuation marker plus eight bits
per byte and an end marker), so empty strings, embedded zero bytes, and prefix
keys are distinct. `PatriciaExtract.v` generates both APIs under
`patricia/extracted/`. Native extraction maps integer keys, prefixes, masks,
and routing operations to OCaml `int`, and maps string bit lookup and
first-difference scanning to allocation-free operations on OCaml strings.

The positive-key proof file currently establishes, without axioms:

- empty/singleton lookup, `mem`, same-key and different-key `set`, and
  key-aware `map` laws;
- representative soundness and lookup/`wf` correctness for compatible and
  disjoint `join` operations;
- simultaneous lookup correctness and `wf` preservation by `set`;
- general `remove` lookup correctness and `wf` preservation;
- lookup correctness and `wf` preservation by `map_filter`, `map_left`, and
  `map_right`;
- `fold` agreement with `elements`;
- `elements` soundness, completeness on `wf` trees, and unique keys;
- extensional correctness of `beq` on `wf` trees;
- sufficiency of the public combine fuel bound for every recursive call shape;
- general lookup correctness and `wf` preservation by `combine_fuel` and the
  public `combine`, for the standard finite-map condition
  `f None None = None`;
- highest-differing-bit prefix agreement and bit separation.

The direct-string proof files currently establish, without axioms:

- injectivity of the prefix-free bit view, including character-bit
  injectivity and the fact that bits past the encoded end are false;
- an exact specification of the bounded first-difference scan: unequal
  strings have a differing position, the bits differ there, and every earlier
  bit agrees;
- the logical specification of `agrees_before`;
- a structural routing invariant for string trees and preservation of that
  invariant by smart branch collapse, `remove`, key-aware `map`, and general
  `set`, including fresh-key insertion;
- strict increase of descendant string split positions, derived from that
  routing invariant;
- representative and routed-leaf soundness;
- two-way agreement between `get` and `elements` on well-formed trees,
  completeness of lookup, unique element keys, and unique bindings;
- the general lookup specification for `remove`, plus the corresponding
  `elements` filtering specification;
- the unconditional `set` lookup law and well-formedness preservation,
  including fresh and existing keys;
- `fold` agreement with `elements`, the key-aware `map` lookup law, and
  well-formedness/lookup laws for `map_filter`, `map_left`, and `map_right`
  (the latter two under `f None None = None`).

`join_disjoint_correct_wf` proves the string-tree join law under its explicit
prefix/bit-separation preconditions. Generic `combine` remains a proof
obligation; the randomized string tests exercise it, but are not substitutes
for its general Rocq specification.

It then runs deterministic randomized OCaml tests against reference maps. The
positive suite exercises point updates, removal, generic and deletion-capable
combines, both biased unions, element ordering, routing/canonicality, and
keys at every native bit boundary through `max_int`. The string suite checks
the same map operations and structural routing invariants over empty strings,
embedded NUL bytes, prefix-related strings, non-ASCII bytes, long common
prefixes, and generated arbitrary byte strings. These are executable tests,
not Rocq proofs or validation of the custom extraction constants.

This is a design sketch, not a drop-in `Maps.TREE` implementation. Constructors
remain visible. The integer proofs use unbounded positive keys, while extraction
uses bounded OCaml `int`; callers must therefore supply keys in
`1 .. max_int`. The string tree uses native OCaml strings and integer bit
positions. These custom extraction refinements form an explicit
performance/correctness boundary: their equivalence to the pure Rocq functions
is trusted, rather than proved inside Rocq.
