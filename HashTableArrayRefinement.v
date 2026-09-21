(** The explicit foreign boundary for the private OCaml array sequence.

    This file does not model OCaml heaps.  Instead, clients supply a sequence
    implementation with a logical list view and fresh-update evidence.  The
    theorems below show that those contracts are exactly sufficient to refine
    the modeled [pseq] operations used by the extracted native HAMT. *)

From Stdlib Require Import List.
Import ListNotations.

Require Import HashTable HashTableBits HashTableNative.

Set Implicit Arguments.

Record array_sequence_contract : Type := {
  array_seq : Type -> Type;
  array_view : forall {A}, array_seq A -> list A;
  array_of_list : forall {A}, list A -> array_seq A;
  array_get : forall {A}, nat -> array_seq A -> option A;
  array_insert : forall {A}, nat -> A -> array_seq A -> array_seq A;
  array_replace : forall {A}, nat -> A -> array_seq A -> array_seq A;
  array_remove : forall {A}, nat -> array_seq A -> array_seq A;
  array_fresh : forall {A}, array_seq A -> array_seq A -> Prop;
  array_of_list_view : forall A (items : list A),
      array_view (array_of_list items) = items;
  array_get_view : forall A index (items : array_seq A),
      array_get index items = nth_error (array_view items) index;
  array_insert_view : forall A index (item : A) (items : array_seq A),
      array_view (array_insert index item items) =
        dense_insert index item (array_view items);
  array_replace_view : forall A index (item : A) (items : array_seq A),
      array_view (array_replace index item items) =
        dense_replace index item (array_view items);
  array_remove_view : forall A index (items : array_seq A),
      array_view (array_remove index items) =
        dense_remove index (array_view items);
  array_insert_fresh : forall A index (item : A) (items : array_seq A),
      array_fresh items (array_insert index item items);
  array_replace_fresh : forall A index (item : A) (items : array_seq A),
      array_fresh items (array_replace index item items);
  array_remove_fresh : forall A index (items : array_seq A),
      array_fresh items (array_remove index items)
}.

Definition array_pseq_refines (C : array_sequence_contract) {A}
    (target : array_seq C A) (model : pseq A) : Prop :=
  array_view C target = pseq_view model.

Lemma array_pseq_of_list_refines :
  forall (C : array_sequence_contract) A (items : list A),
    array_pseq_refines C (array_of_list C items) (pseq_of_list items).
Proof.
  intros. unfold array_pseq_refines, pseq_of_list.
  apply array_of_list_view.
Qed.

Lemma array_pseq_get_refines :
  forall (C : array_sequence_contract) A index
         (target : array_seq C A) (model : pseq A),
    array_pseq_refines C target model ->
    array_get C index target = pseq_get index model.
Proof.
  intros C A index target model Hrefines.
  unfold array_pseq_refines in Hrefines.
  rewrite array_get_view, pseq_get_view, Hrefines. reflexivity.
Qed.

Lemma array_pseq_insert_refines :
  forall (C : array_sequence_contract) A index (item : A)
         (target : array_seq C A) (model : pseq A),
    array_pseq_refines C target model ->
    array_pseq_refines C (array_insert C index item target)
      (pseq_insert index item model).
Proof.
  intros C A index item target model Hrefines.
  unfold array_pseq_refines in *.
  rewrite array_insert_view, pseq_insert_view, Hrefines. reflexivity.
Qed.

Lemma array_pseq_replace_refines :
  forall (C : array_sequence_contract) A index (item : A)
         (target : array_seq C A) (model : pseq A),
    array_pseq_refines C target model ->
    array_pseq_refines C (array_replace C index item target)
      (pseq_replace index item model).
Proof.
  intros C A index item target model Hrefines.
  unfold array_pseq_refines in *.
  rewrite array_replace_view, pseq_replace_view, Hrefines. reflexivity.
Qed.

Lemma array_pseq_remove_refines :
  forall (C : array_sequence_contract) A index
         (target : array_seq C A) (model : pseq A),
    array_pseq_refines C target model ->
    array_pseq_refines C (array_remove C index target)
      (pseq_remove index model).
Proof.
  intros C A index target model Hrefines.
  unfold array_pseq_refines in *.
  rewrite array_remove_view, pseq_remove_view, Hrefines. reflexivity.
Qed.
