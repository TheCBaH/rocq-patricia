(** Deterministic, bounded hashes for reference-map tests.

    These functions model the wrapper boundary: every result is in
    [[0, 2^30)].  They deliberately avoid depending on the process-randomized
    hash used by OCaml's generic hash functions. *)

val bound : int
(** [bound] is [2^30]. *)

val normalize : int -> int
(** [normalize raw] retains the low 30 bits of [raw]. *)

val int : seed:int -> int -> int
(** A deterministic bounded hash for integer keys. *)

val string : seed:int -> string -> int
(** A deterministic bounded hash for byte strings. *)

val constant : seed:int -> 'a -> int
(** A bounded constant hash for deliberate collision tests. *)
