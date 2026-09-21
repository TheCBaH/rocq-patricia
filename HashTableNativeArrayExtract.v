(** Extraction of the modeled native HAMT with only its persistent-sequence
    interface realized by the private OCaml array adapter.  Source lists remain
    ordinary extracted lists; this mapping is deliberately local to [pseq]. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
Require Import HashTableSpec HashTableBits HashTableBucket HashTable HashTableNative.

Extraction Language OCaml.
Set Extraction Output Directory "hashtable_native_array_extracted".

Extract Inductive HashTableNative.pseq => "HashTablePrimitives.t"
  [ "(fun items -> HashTablePrimitives.of_list items)" ].
Extract Constant HashTableNative.pseq_view => "HashTablePrimitives.to_list".
Extract Constant HashTableNative.pseq_of_list => "HashTablePrimitives.of_list".
Extract Constant HashTableNative.pseq_get => "HashTablePrimitives.get".
Extract Constant HashTableNative.pseq_insert => "HashTablePrimitives.insert".
Extract Constant HashTableNative.pseq_replace => "HashTablePrimitives.replace".
Extract Constant HashTableNative.pseq_remove => "HashTablePrimitives.remove".

Separate Extraction
  HashTableNative.pseq_of_list
  HashTableNative.pseq_get HashTableNative.pseq_insert
  HashTableNative.pseq_replace HashTableNative.pseq_remove
  HashTable.get_tree
  HashTableNative.source_of_native HashTableNative.native_of_source
  HashTableNative.native_get HashTableNative.native_set HashTableNative.native_remove.
