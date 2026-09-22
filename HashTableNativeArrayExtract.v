(** Extraction of the modeled native HAMT with only its persistent-sequence
    interface realized by the private OCaml array adapter.  Source lists remain
    ordinary extracted lists; this mapping is deliberately local to [pseq]. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.
Require Import HashTableSpec HashTableBits HashTableNativeBits HashTableBucket HashTable HashTableNative.

Extraction Language OCaml.
Set Extraction Output Directory "hashtable_native_array_extracted".

Extract Inductive HashTableNative.pseq => "HashTablePrimitives.t"
  [ "(fun items -> HashTablePrimitives.of_list items)" ].
Extract Constant HashTableNative.pseq_view => "HashTablePrimitives.to_list".
Extract Constant HashTableNative.pseq_of_list => "HashTablePrimitives.of_list".
Extract Constant HashTableNative.pseq_is_empty => "HashTablePrimitives.is_empty".
Extract Constant HashTableNative.pseq_get => "HashTablePrimitives.get".
Extract Constant HashTableNative.pseq_insert => "HashTablePrimitives.insert".
Extract Constant HashTableNative.pseq_replace => "HashTablePrimitives.replace".
Extract Constant HashTableNative.pseq_remove => "HashTablePrimitives.remove".

Extract Constant HashTableNativeBits.native_chunk => "HashTableScalarPrimitives.chunk".
Extract Constant HashTableNativeBits.native_bitmap_bit => "HashTableScalarPrimitives.bitmap_bit".
Extract Constant HashTableNativeBits.native_bitmap_has => "HashTableScalarPrimitives.bitmap_has".
Extract Constant HashTableNativeBits.native_rank => "HashTableScalarPrimitives.rank".
Extract Constant HashTableNativeBits.native_bitmap_insert => "HashTableScalarPrimitives.bitmap_insert".
Extract Constant HashTableNativeBits.native_bitmap_remove => "HashTableScalarPrimitives.bitmap_remove".

Separate Extraction
  HashTableNative.pseq_of_list
  HashTableNative.pseq_is_empty
  HashTableNative.pseq_get HashTableNative.pseq_insert
  HashTableNative.pseq_replace HashTableNative.pseq_remove
  HashTable.get_tree
  HashTableNative.source_of_native HashTableNative.native_of_source
  HashTableNative.native_get HashTableNative.native_set HashTableNative.native_remove
  HashTableNative.native_empty HashTableNative.native_table_is_empty
  HashTableNative.native_table_get HashTableNative.native_table_mem
  HashTableNative.native_table_set HashTableNative.native_table_remove
  HashTableNative.native_table_elements HashTableNative.native_table_of_list.
