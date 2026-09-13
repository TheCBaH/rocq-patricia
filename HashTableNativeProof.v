(** Refinement theorems for the modeled compact-sequence backend.

    These theorems are about the Rocq [pseq] model.  They do not establish an
    OCaml array heap theorem; that remaining target obligation is recorded in
    the tracker. *)

From Stdlib Require Import NArith.

Require Import HashTable HashTableNative.

Set Implicit Arguments.

Lemma native_get_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_get eqb fuel depth full_hash key native =
    get_tree eqb fuel depth full_hash key source.
Proof.
  intros K A eqb fuel depth full_hash key native source Hrefines.
  unfold native_refines in Hrefines. subst source.
  apply native_get_refines.
Qed.

Lemma native_set_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_refines (native_set eqb fuel depth full_hash key value native)
      (set_tree eqb fuel depth full_hash key value source).
Proof.
  intros K A eqb fuel depth full_hash key value native source Hrefines.
  unfold native_refines in *. subst source.
  apply native_set_refines.
Qed.

Lemma native_remove_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_refines (native_remove eqb fuel depth full_hash key native)
      (remove_tree eqb fuel depth full_hash key source).
Proof.
  intros K A eqb fuel depth full_hash key native source Hrefines.
  unfold native_refines in *. subst source.
  apply native_remove_refines.
Qed.
