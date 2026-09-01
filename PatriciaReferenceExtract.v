From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt
  ExtrOcamlNativeString.
Require Import PatriciaBits Patricia StringBits StringPatricia.

Extraction Language OCaml.
Set Extraction Output Directory "reference_extracted".

(** [ExtrOcamlNativeString]'s constructor eliminator calls OCaml's [String]
    module.  Inline logical length as the corresponding native primitive so
    separate extraction does not emit a shadowing compilation unit also named
    [String].  This is representation plumbing, not a Patricia algorithm
    replacement. *)
Extract Inlined Constant String.length => "Stdlib.String.length".

(** Proof-aligned executable reference backend.

    Unlike [PatriciaExtract], this extraction unit contains no Patricia-specific
    [Extract Constant] realizers.  Its map operations, routing functions,
    logical string positions, representatives, updates, fuelled combines, and
    biased unions are therefore generated directly from their Rocq definitions.

    The standard-library native [int] and string extraction mappings remain in
    use so this backend accepts the same test inputs as the optimized backend.
    They are still part of the documented extraction trust boundary; the
    purpose of this backend is specifically to detect discrepancies introduced
    by the handwritten Patricia optimizations. *)

Separate Extraction
  PatriciaBits.mask_above
  Patricia.empty Patricia.is_empty Patricia.singleton Patricia.get Patricia.mem
  Patricia.set Patricia.remove Patricia.of_list Patricia.map_filter Patricia.map_left
  Patricia.map_right Patricia.replace_binding Patricia.combine_leaf_left
  Patricia.combine_leaf_right Patricia.combine
  Patricia.union_left Patricia.union_right
  Patricia.map Patricia.fold Patricia.elements Patricia.beq
  StringBits.bit_at StringBits.first_diff StringBits.agrees_before
  StringBits.agrees_before_bounded
  StringPatricia.empty StringPatricia.is_empty StringPatricia.singleton
  StringPatricia.representative StringPatricia.branch StringPatricia.branch_at
  StringPatricia.join StringPatricia.map_filter StringPatricia.map_left
  StringPatricia.map_right StringPatricia.replace_binding
  StringPatricia.combine_leaf_left StringPatricia.combine_leaf_right
  StringPatricia.get StringPatricia.mem StringPatricia.set StringPatricia.remove
  StringPatricia.of_list
  StringPatricia.combine StringPatricia.union_left StringPatricia.union_right
  StringPatricia.map StringPatricia.fold StringPatricia.elements
  StringPatricia.beq.
