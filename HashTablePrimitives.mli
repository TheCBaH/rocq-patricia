(** Private-storage sequence primitives for the compact HAMT backend.
    Changed updates return fresh storage; a missing bucket removal may reuse
    its input because the source bucket worker returns it unchanged. *)

type 'a t

val empty : unit -> 'a t
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val length : 'a t -> int
val is_empty : 'a t -> bool
val get : int -> 'a t -> 'a option
val insert : int -> 'a -> 'a t -> 'a t
val replace : int -> 'a -> 'a t -> 'a t
val remove : int -> 'a t -> 'a t
val bucket_get : ('k -> 'k -> bool) -> 'k -> ('k * 'v) t -> int -> int -> 'v option
val bucket_set : ('k -> 'k -> bool) -> 'k -> 'v -> ('k * 'v) t -> int -> int -> ('k * 'v) t
val bucket_remove : ('k -> 'k -> bool) -> 'k -> ('k * 'v) t -> int -> int -> ('k * 'v) t
