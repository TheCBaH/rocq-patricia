(* Frozen handwritten string primitives from e7f5cd6:PatriciaExtract.v,
   for acceptance comparisons only. Never linked into the public library. *)

(** val bit_at : string -> int -> bool **)

let bit_at s token =
  let byte = token lsr 4 and tag = token land 15 in
  byte < Stdlib.String.length s &&
  (tag = 0 || (tag <= 8 &&
    ((Char.code (Stdlib.String.unsafe_get s byte) lsr (8 - tag)) land 1) <> 0))

(** val first_diff : string -> string -> int option **)

let first_diff = (fun left right ->
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
     in scan 0)

(** val agrees_before : string -> string -> int -> bool **)

let agrees_before left right split =
  match first_diff left right with
  | Some differing -> (<=) split differing
  | None -> true

(** val agrees_before_bounded : string -> string -> int -> bool **)

let agrees_before_bounded = (fun left right split ->
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
     in scan left right left_length right_length common split_byte split_tag 0)
