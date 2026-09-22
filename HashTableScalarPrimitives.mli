(** OCaml realizers for the bounded scalar extraction boundary.

    Inputs are non-negative extracted [N] values.  HAMT public routing calls
    them only with a 30-bit hash, depth at most six, a 32-bit bitmap, and a
    slot in [0,31].  The source theorems model their results; this module is a
    reviewed target obligation, not a kernel proof of OCaml execution. *)

val chunk : int -> int -> int
val bitmap_bit : int -> int
val bitmap_has : int -> int -> bool
val rank : int -> int -> int
val bitmap_insert : int -> int -> int
val bitmap_remove : int -> int -> int
