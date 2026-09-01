(** Abstract public interface to the extracted positive-key Patricia map.

    Values of type ['a t] can only be produced by the smart operations below;
    the extracted tree constructors and proof-internal workers are deliberately
    not part of this interface.  Keys must be created through [Key], which
    rejects integers outside the extracted positive-key domain. *)

module Key : sig
  type t

  val of_int : int -> t option
  val of_int_exn : int -> t
  val to_int : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

type key = Key.t
type 'a t

val empty : 'a t
val is_empty : 'a t -> bool
val singleton : key -> 'a -> 'a t
val get : key -> 'a t -> 'a option
val mem : key -> 'a t -> bool
val set : key -> 'a -> 'a t -> 'a t
val remove : key -> 'a t -> 'a t

(** [of_list bindings] bulk-loads bindings into a map.  If a key occurs more
    than once, its first occurrence in [bindings] wins. *)
val of_list : (key * 'a) list -> 'a t

val map : (key -> 'a -> 'b) -> 'a t -> 'b t
val map_filter : (key -> 'a -> 'b option) -> 'a t -> 'b t

(** The three possible cases for a key represented by at least one input map.
    Returning [None] omits that key from the result. *)
type ('a, 'b, 'c) combiner = {
  left_only : 'a -> 'c option;
  right_only : 'b -> 'c option;
  both : 'a -> 'b -> 'c option;
}

(** [combine f left right] applies the corresponding field of [f] at every
    key represented by [left] or [right].  A key absent from both maps is
    always absent from the result, so the finite-map condition corresponding
    to [f None None = None] is enforced by this interface. *)
val combine : ('a, 'b, 'c) combiner -> 'a t -> 'b t -> 'c t

val union_left : 'a t -> 'a t -> 'a t
val union_right : 'a t -> 'a t -> 'a t
val elements : 'a t -> (key * 'a) list
val fold : ('b -> key -> 'a -> 'b) -> 'a t -> 'b -> 'b
val beq : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
