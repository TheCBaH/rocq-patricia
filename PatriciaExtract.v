From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt
  ExtrOcamlNativeString.
Require Import PatriciaBits Patricia StringBits StringPatricia.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".

(** The integer-key API is extracted to OCaml's native [int].  The proof-side
    [positive]/[N] model is unbounded; as with [ExtrOcamlZInt], clients must
    keep keys positive and within [max_int].  These realizers make all hot
    Patricia routing operations fixed-width native operations. *)
Extract Inlined Constant BinPos.Pos.eqb => "(=)".
Extract Inlined Constant BinNat.N.eqb => "(=)".
Extract Inlined Constant BinNat.N.ltb => "(<)".
Extract Constant PatriciaBits.word => "(fun k -> k)".
Extract Constant PatriciaBits.prefix => "(fun k mask -> k lsr (mask + 1))".
Extract Constant PatriciaBits.matches_prefix =>
  "(fun k p mask -> (k lsr (mask + 1)) = p)".
Extract Constant PatriciaBits.zero_bit =>
  "(fun k mask -> ((k lsr mask) land 1) = 0)".
Extract Constant PatriciaBits.highest_differing_bit =>
  "(fun left right ->
     let rec log2 n bit =
       if n lsr 1 = 0 then bit else log2 (n lsr 1) (bit + 1)
     in log2 (left lxor right) 0)".
Extract Constant PatriciaBits.mask_above => "(fun high low -> low < high)".

(** Proof-side definitions remain pure Rocq.  These extraction refinements
    give the direct string implementation constant-time byte access and a
    single allocation-free first-difference scan over native OCaml strings. *)
Extract Constant StringBits.bit_at =>
  "(fun s n ->
     let byte = n / 9 and offset = n mod 9 in
     if byte >= Stdlib.String.length s then false
     else if offset = 0 then true
     else ((Char.code (Stdlib.String.get s byte) lsr (8 - offset)) land 1) <> 0)".

Extract Constant StringBits.first_diff =>
  "(fun left right ->
     if left = right then None else
     let limit = 9 * max (Stdlib.String.length left) (Stdlib.String.length right) + 1 in
     let bit s n =
       let byte = n / 9 and offset = n mod 9 in
       if byte >= Stdlib.String.length s then false
       else if offset = 0 then true
       else ((Char.code (Stdlib.String.get s byte) lsr (8 - offset)) land 1) <> 0
     in
     let rec scan n =
       if n >= limit then None
       else if bit left n <> bit right n then Some n else scan (n + 1)
     in scan 0)".

Separate Extraction
  Patricia.empty Patricia.is_empty Patricia.singleton Patricia.get Patricia.mem
  Patricia.set Patricia.remove Patricia.combine
  Patricia.union_left Patricia.union_right
  Patricia.map Patricia.fold Patricia.elements Patricia.beq
  StringPatricia.empty StringPatricia.is_empty StringPatricia.singleton
  StringPatricia.get StringPatricia.mem StringPatricia.set StringPatricia.remove
  StringPatricia.combine StringPatricia.union_left StringPatricia.union_right
  StringPatricia.map StringPatricia.fold StringPatricia.elements.
