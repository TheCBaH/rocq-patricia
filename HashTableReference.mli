(** Stable package name for the separately extracted list-source backend.

    The generated [HashTable] module remains an implementation detail of the
    extraction directory.  Public wrappers should depend on this name instead. *)

include module type of HashTable
