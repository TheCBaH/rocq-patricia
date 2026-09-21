(** Abstract wrapper over the array-bound extracted native HAMT.  This is kept
    separate from [HashMap] while its foreign array contract remains explicit. *)

module type KEY = HashMap.KEY

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
