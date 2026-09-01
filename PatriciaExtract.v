From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt
  ExtrOcamlNativeString.
Require Import PatriciaBits Patricia PatriciaUnion StringBits StringPatricia
  StringPatriciaUnion.

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

(** The generic native union is extracted normally; physical equality is its
    only target-specific primitive. *)
Extract Inlined Constant PatriciaUnion.native_same => "(==)".

(** [Patricia.combine] is the proved, fuel-free structural worker.  Extract it
    directly so the optimized backend no longer substitutes a handwritten
    general merge implementation. *)

(** A biased union maps one-sided bindings identically. Reuse those subtrees
    directly, and join disjoint prefixes immediately. Physical-identity checks
    preserve the left tree (or the containing right tree) when a recursive
    merge makes no observable change. The companion source worker is the
    functional oracle; refining these [==] decisions requires a heap model. *)
Extract Constant Patricia.union_left =>
  "(fun first second ->
     let rec union left right =
       match left, right with
       | Empty, tree | tree, Empty -> tree
       | (Leaf (left_key, _) as leaf), Leaf (right_key, _)
         when left_key = right_key -> leaf
       | Leaf (key, value), tree -> set key value tree
       | tree, Leaf (key, value) ->
           (match get key tree with Some _ -> tree | None -> set key value tree)
       | (Branch (prefix_left, mask_left, left_left, right_left) as left_tree),
         (Branch (prefix_right, mask_right, left_right, right_right) as right_tree) ->
           if mask_left = mask_right && prefix_left = prefix_right then
             let merged_left = union left_left left_right in
             let merged_right = union right_left right_right in
             if merged_left == left_left && merged_right == right_left then left_tree
             else Branch (prefix_left, mask_left, merged_left, merged_right)
           else if mask_above mask_left mask_right then
             match representative right with
             | Some key when matches_prefix key prefix_left mask_left ->
                 if zero_bit key mask_left then
                   let merged = union left_left right_tree in
                   if merged == left_left then left_tree
                   else Branch (prefix_left, mask_left, merged, right_left)
                 else
                   let merged = union right_left right_tree in
                   if merged == right_left then left_tree
                   else Branch (prefix_left, mask_left, left_left, merged)
             | _ -> join left_tree right_tree
           else if mask_above mask_right mask_left then
             match representative left with
             | Some key when matches_prefix key prefix_right mask_right ->
                 if zero_bit key mask_right then
                   let merged = union left_tree left_right in
                   if merged == left_right then right_tree
                   else Branch (prefix_right, mask_right, merged, right_right)
                 else
                   let merged = union left_tree right_right in
                   if merged == right_right then right_tree
                   else Branch (prefix_right, mask_right, left_right, merged)
             | _ -> join left_tree right_tree
           else join left_tree right_tree
     in union first second)".

Extract Constant Patricia.union_right =>
  "(fun first second -> union_left second first)".

(** Proof-side definitions remain pure Rocq.  Extracted string branches use a
    packed critical-bit token [(byte_index << 4) | tag], where tag zero is the
    continuation marker and tags 1--8 are the byte's bits from most to least
    significant.  Token order is the order of the proof-side logical bit
    positions, but routing needs only shifts and masks rather than division
    and remainder by nine. *)
Extract Constant StringBits.bit_at =>
  "(fun s n ->
     let byte = n lsr 4 and tag = n land 15 in
     byte < Stdlib.String.length s &&
       (tag = 0 ||
        (tag <= 8 &&
         ((Char.code (Stdlib.String.unsafe_get s byte) lsr (8 - tag)) land 1) <> 0)))".

Extract Inlined Constant StringPatriciaUnion.native_same => "(==)".

Extract Constant StringBits.first_diff =>
  "(fun left right ->
     if left == right then None else
     let left_length = Stdlib.String.length left
     and right_length = Stdlib.String.length right in
     let common = if left_length < right_length then left_length else right_length in
     let rec scan byte =
       if byte = common then
         if left_length = right_length then None else Some (byte lsl 4)
       else
         let difference =
           Char.code (Stdlib.String.unsafe_get left byte) lxor
           Char.code (Stdlib.String.unsafe_get right byte)
         in
         if difference = 0 then scan (byte + 1)
         else
           let rec leading_zeroes count mask =
             if difference land mask <> 0 then count
             else leading_zeroes (count + 1) (mask lsr 1)
           in
           Some ((byte lsl 4) lor (1 + leading_zeroes 0 128))
     in scan 0)".

(** The source worker is proved equal to logical [agrees_before].  Under the
    existing packed-position refinement, scan complete bytes strictly before
    the split byte and only the relevant high bits of its final byte.  This
    returns the Boolean directly and does not allocate a [first_diff] option. *)
Extract Constant StringBits.agrees_before_bounded =>
  "(fun left right split ->
     let split_byte = split lsr 4
     and split_tag = split land 15
     and left_length = Stdlib.String.length left
     and right_length = Stdlib.String.length right in
     let common =
       if left_length < right_length then left_length else right_length
     in
     let rec scan left right left_length right_length common
                  split_byte split_tag byte =
       if byte = split_byte then
         if split_tag = 0 then true
         else
           let left_present = byte < left_length
           and right_present = byte < right_length in
           if left_present <> right_present then false
           else if not left_present then true
           else
             let mask = (255 lsl (9 - split_tag)) land 255 in
             ((Char.code (Stdlib.String.unsafe_get left byte) lxor
               Char.code (Stdlib.String.unsafe_get right byte)) land mask) = 0
       else if byte = common then left_length = right_length
       else if Stdlib.String.unsafe_get left byte <>
                    Stdlib.String.unsafe_get right byte then false
       else scan left right left_length right_length common
                 split_byte split_tag (byte + 1)
     in scan left right left_length right_length common split_byte split_tag 0)".

(** Every well-formed branch caches a resident key in its sample field;
    [StringPatriciaProof.wf_cached_sample_resident] exposes that invariant, and
    all public-operation preservation theorems maintain it.  Use the cache in
    native code rather than walking to a leaf.  The pure [representative] may
    select a different resident key, so full native refinement must rely on
    representative-choice independence rather than definitional equality. *)
Extract Constant StringPatricia.representative =>
  "(function
     | Empty -> None
     | Leaf (key, _) -> Some key
     | Branch (sample, _, _, _) -> Some sample)".

(** Fuse routed-leaf discovery with persistent reconstruction.  A local
    exception carries a fresh key's discriminator up to the first ancestor
    below which it belongs.  Existing-key replacement and fresh insertion
    therefore each route through the input only once. *)
Extract Constant StringPatricia.set =>
  "(fun key value root ->
     let fresh = Leaf (key, value) in
     let exception Fresh_key of int in
     let rec descend tree =
       match tree with
       | Empty -> fresh
       | Leaf (stored, _) ->
           (match first_diff key stored with
            | None -> fresh
            | Some differing -> raise (Fresh_key differing))
       | Branch (sample, split, left, right) ->
           if bit_at key split then
             (try Branch (sample, split, left, descend right) with
              | (Fresh_key differing as pending) ->
                  if differing < split then raise pending
                  else Branch (sample, split, left,
                         branch_at key differing fresh right))
           else
             (try Branch (sample, split, descend left, right) with
              | (Fresh_key differing as pending) ->
                  if differing < split then raise pending
                  else Branch (sample, split,
                         branch_at key differing fresh left, right))
     in
     try descend root with
     | Fresh_key differing -> branch_at key differing fresh root)".

(** [StringPatricia.combine] is likewise the proved fuel-free structural
    worker, so extraction retains it instead of replacing it with native
    handwritten merge code. *)

(** Biased union has identity behavior on one-sided subtrees, so it can share
    them instead of going through generic [combine]. Disjoint prefixes are
    joined immediately; containment recurses only into the potentially
    overlapping child. The source changed worker specifies its observable map
    result; the physical [==] tests remain a native-refinement obligation. *)
Extract Constant StringPatricia.union_left =>
  "(fun first second ->
     let rec union left right =
       match left, right with
       | Empty, tree | tree, Empty -> tree
       | (Leaf (left_key, _) as leaf), Leaf (right_key, _) when left_key = right_key ->
           leaf
       | Leaf (key, value), tree -> set key value tree
       | tree, Leaf (key, value) ->
           (match get key tree with
            | Some _ -> tree
            | None -> set key value tree)
       | (Branch (sample_left, split_left, left_left, right_left) as left_tree),
         (Branch (sample_right, split_right, left_right, right_right) as right_tree) ->
           if split_left = split_right then
             if agrees_before_bounded sample_left sample_right split_left then
               let merged_left = union left_left left_right in
               let merged_right = union right_left right_right in
               if merged_left == left_left && merged_right == right_left then left_tree
               else Branch (sample_left, split_left, merged_left, merged_right)
             else join left_tree right_tree
           else if split_left < split_right then
             if agrees_before_bounded sample_left sample_right split_left then
               if bit_at sample_right split_left then
                 let merged = union right_left right_tree in
                 if merged == right_left then left_tree
                 else Branch (sample_left, split_left, left_left, merged)
               else
                 let merged = union left_left right_tree in
                 if merged == left_left then left_tree
                 else Branch (sample_left, split_left, merged, right_left)
             else join left_tree right_tree
           else if agrees_before_bounded sample_left sample_right split_right then
             if bit_at sample_left split_right then
               let merged = union left_tree right_right in
               if merged == right_right then right_tree
               else Branch (sample_right, split_right, left_right, merged)
             else
               let merged = union left_tree left_right in
               if merged == left_right then right_tree
               else Branch (sample_right, split_right, merged, right_right)
           else join left_tree right_tree
     in union first second)".

Extract Constant StringPatricia.union_right =>
  "(fun first second -> union_left second first)".

Separate Extraction
  PatriciaBits.mask_above
  Patricia.empty Patricia.is_empty Patricia.singleton Patricia.get Patricia.mem
  Patricia.set Patricia.remove Patricia.of_list Patricia.map_filter Patricia.map_left
  Patricia.map_right Patricia.replace_binding Patricia.combine_leaf_left
  Patricia.combine_leaf_right Patricia.combine
  Patricia.union_left Patricia.union_right
  PatriciaUnion.union_left_specialized PatriciaUnion.union_right_specialized
  PatriciaUnion.union_left_specialized_changed
  PatriciaUnion.union_left_specialized_changed_result
  PatriciaUnion.union_left_specialized_changed_fuel
  PatriciaUnion.union_left_specialized_changed_fuel_result
  PatriciaUnion.union_left_native_default
  PatriciaUnion.union_left_native_fuel_default
  PatriciaUnion.union_left_native_fuel_inline_default
  PatriciaUnion.union_right_specialized_changed
  PatriciaUnion.union_right_specialized_changed_result
  Patricia.map Patricia.fold Patricia.elements Patricia.beq
  StringBits.bit_at StringBits.first_diff StringBits.agrees_before
  StringBits.agrees_before_bounded
  StringPatricia.empty StringPatricia.is_empty StringPatricia.singleton
  StringPatricia.representative StringPatricia.branch StringPatricia.branch_at
  StringPatricia.join StringPatricia.map_filter StringPatricia.map_left
  StringPatricia.map_right StringPatricia.replace_binding
  StringPatricia.combine_leaf_left StringPatricia.combine_leaf_right
  StringPatricia.get StringPatricia.mem StringPatricia.set_one_descent
  StringPatricia.set StringPatricia.remove StringPatricia.of_list
  StringPatricia.combine StringPatricia.union_left StringPatricia.union_right
  StringPatriciaUnion.union_left_specialized
  StringPatriciaUnion.union_right_specialized
  StringPatriciaUnion.union_left_specialized_changed
  StringPatriciaUnion.union_left_specialized_changed_result
  StringPatriciaUnion.union_left_specialized_changed_fuel
  StringPatriciaUnion.union_left_specialized_changed_fuel_result
  StringPatriciaUnion.union_left_native_default
  StringPatriciaUnion.union_left_native_fuel_default
  StringPatriciaUnion.union_right_specialized_changed
  StringPatriciaUnion.union_right_specialized_changed_result
  StringPatricia.map StringPatricia.fold StringPatricia.elements
  StringPatricia.beq.
