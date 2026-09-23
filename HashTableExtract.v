(** Separate extraction of the modeled native backend.

    This artifact preserves modeled native workers.  It deliberately does not
    bind [pseq] to OCaml arrays yet: that binding needs recursive compact
    update/removal realization and corresponding view/refinement proofs. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
Require Import HashTableSpec HashTableBits HashTableBucket HashTable HashTableNative.

Extraction Language OCaml.
Set Extraction Output Directory "hashtable_extracted".

Separate Extraction
  HashTableNative.pseq_empty HashTableNative.pseq_of_list
  HashTableNative.pseq_get HashTableNative.pseq_insert
  HashTableNative.pseq_replace HashTableNative.pseq_remove
  HashTable.get_tree HashTable.set_tree HashTable.remove_tree
  HashTableNative.source_of_native HashTableNative.native_of_source
  HashTableNative.native_get HashTableNative.native_get_depth0
  HashTableNative.native_table_get
  HashTableNative.native_set HashTableNative.native_remove.
