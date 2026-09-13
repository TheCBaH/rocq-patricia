(** Proof-aligned reference extraction for the list-backed HAMT source. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
Require Import HashTableSpec HashTableBits HashTableBucket HashTable.

Extraction Language OCaml.
Set Extraction Output Directory "hashtable_reference_extracted".

Separate Extraction
  HashTable.empty HashTable.is_empty HashTable.elements
  HashTable.get HashTable.mem HashTable.set HashTable.remove
  HashTable.singleton HashTable.of_list
  HashTable.bindings HashTable.join_worker.
