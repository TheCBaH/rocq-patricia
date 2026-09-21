(** Public persistent hash-map interface.  Node constructors, depth, routing
    hashes, and extraction details remain private to this wrapper. *)

module type KEY = sig
  type t

  (** [equal] must implement the map's key equivalence relation. *)
  val equal : t -> t -> bool

  (** [hash] may return any OCaml [int].  The wrapper retains its low 30 bits.
      Equivalent keys must return the same normalized hash for a fixed seed. *)
  val hash : seed:int -> t -> int
end

module Make (Key : KEY) : sig
  type key = Key.t
  type 'a t

  (** The seed is retained by all maps derived from this value. *)
  val empty : seed:int -> 'a t
  (** [singleton ~seed key value] retains [seed]. *)
  val singleton : seed:int -> key -> 'a -> 'a t
  val is_empty : 'a t -> bool
  val get : key -> 'a t -> 'a option
  val mem : key -> 'a t -> bool
  (** Setting an equivalent key replaces its value while retaining the stored
      key representative already present in the map. *)
  val set : key -> 'a -> 'a t -> 'a t
  val remove : key -> 'a t -> 'a t
  (** [of_list] retains [seed].  Its first binding for each equivalent key
      wins, including that binding's key representative. *)
  val of_list : seed:int -> (key * 'a) list -> 'a t
  (** Enumerates the resident key representatives and values. *)
  val elements : 'a t -> (key * 'a) list
end
