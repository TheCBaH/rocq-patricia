(** Experimental compact-array backend.

    This backend uses fresh private child arrays through [HashTablePrimitives].
    It is not selected by [HashMap.Make] until the source/refinement and
    differential gates recorded in the tracker are complete. *)

module type KEY = sig
  type t
  val equal : t -> t -> bool
  val hash : seed:int -> t -> int
end

module Make (Key : KEY) : sig
  type key = Key.t
  type 'a t

  val empty : seed:int -> 'a t
  val singleton : seed:int -> key -> 'a -> 'a t
  val is_empty : 'a t -> bool
  val get : key -> 'a t -> 'a option
  val mem : key -> 'a t -> bool
  val set : key -> 'a -> 'a t -> 'a t
  val remove : key -> 'a t -> 'a t
  val of_list : seed:int -> (key * 'a) list -> 'a t
  val elements : 'a t -> (key * 'a) list
end
