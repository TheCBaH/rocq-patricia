(** Separate extraction of the modeled native backend.

    This artifact preserves the source-defined native workers.  It deliberately
    does not bind [pseq] to OCaml arrays yet: that binding needs a recursive
    native worker realization and a corresponding view/refinement proof. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
Require Import HashTableSpec HashTableBits HashTableBucket HashTable HashTableNative.

Extraction Language OCaml.
Set Extraction Output Directory "hashtable_extracted".

Separate Extraction
  HashTableNative.pseq_empty HashTableNative.pseq_of_list
  HashTableNative.pseq_get HashTableNative.pseq_insert
  HashTableNative.pseq_replace HashTableNative.pseq_remove
  HashTableNative.source_of_native HashTableNative.native_of_source
  HashTableNative.native_get HashTableNative.native_set HashTableNative.native_remove.
