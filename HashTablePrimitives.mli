(** Private-storage sequence primitives for the future compact HAMT backend.
    Every mutating-style operation returns fresh storage. *)

type 'a t

val empty : unit -> 'a t
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val length : 'a t -> int
val get : int -> 'a t -> 'a option
val insert : int -> 'a -> 'a t -> 'a t
val replace : int -> 'a -> 'a t -> 'a t
val remove : int -> 'a t -> 'a t
