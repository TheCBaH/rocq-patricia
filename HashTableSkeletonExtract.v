From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Require Import HashTableSpec HashTableSkeleton.

Extraction Language OCaml.
Set Extraction Output Directory "hashtable_skeleton_extracted".

(** This early extraction is only a shape audit.  It keeps the generic
    callbacks and explicit fuel visible in generated code; H3 will replace it
    with the proved reference map under the public [HashTableReference] name. *)
Separate Extraction
  HashTableSpec.normalize_hash
  HashTableSkeleton.slot HashTableSkeleton.join_worker
  HashTableSkeleton.update_worker HashTableSkeleton.prototype_set.
