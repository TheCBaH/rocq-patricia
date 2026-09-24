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
  array_is_empty : forall {A}, array_seq A -> bool;
  array_get : forall {A}, nat -> array_seq A -> option A;
  array_length : forall {A}, array_seq A -> nat;
  array_insert : forall {A}, nat -> A -> array_seq A -> array_seq A;
  array_replace : forall {A}, nat -> A -> array_seq A -> array_seq A;
  array_remove : forall {A}, nat -> array_seq A -> array_seq A;
  array_bucket_get : forall {K A}, (K -> K -> bool) -> K ->
      array_seq (K * A) -> nat -> nat -> option A;
  array_bucket_set : forall {K A}, (K -> K -> bool) -> K -> A ->
      array_seq (K * A) -> nat -> nat -> array_seq (K * A);
  array_bucket_remove : forall {K A}, (K -> K -> bool) -> K ->
      array_seq (K * A) -> nat -> nat -> array_seq (K * A);
  array_fresh : forall {A}, array_seq A -> array_seq A -> Prop;
  array_of_list_view : forall A (items : list A),
      array_view (array_of_list items) = items;
  array_is_empty_view : forall A (items : array_seq A),
      array_is_empty items = true <-> array_view items = [];
  array_get_view : forall A index (items : array_seq A),
      array_get index items = nth_error (array_view items) index;
  array_length_view : forall A (items : array_seq A),
      array_length items = length (array_view items);
  array_insert_view : forall A index (item : A) (items : array_seq A),
      array_view (array_insert index item items) =
        dense_insert index item (array_view items);
  array_replace_view : forall A index (item : A) (items : array_seq A),
      array_view (array_replace index item items) =
        dense_replace index item (array_view items);
  array_remove_view : forall A index (items : array_seq A),
      array_view (array_remove index items) =
        dense_remove index (array_view items);
  array_bucket_get_view : forall K A (eqb : K -> K -> bool) key
      (items : array_seq (K * A)) index remaining,
      array_bucket_get eqb key items index remaining =
        native_bucket_get eqb key (pseq_of_list (array_view items)) index remaining;
  array_bucket_set_view : forall K A (eqb : K -> K -> bool) key value
      (items : array_seq (K * A)) index remaining,
      array_view (array_bucket_set eqb key value items index remaining) =
        pseq_view (native_bucket_set eqb key value
          (pseq_of_list (array_view items)) index remaining);
  array_bucket_remove_view : forall K A (eqb : K -> K -> bool) key
      (items : array_seq (K * A)) index remaining,
      array_view (array_bucket_remove eqb key items index remaining) =
        pseq_view (native_bucket_remove eqb key
          (pseq_of_list (array_view items)) index remaining);
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

Lemma array_pseq_is_empty_refines :
  forall (C : array_sequence_contract) A
         (target : array_seq C A) (model : pseq A),
    array_pseq_refines C target model ->
    array_is_empty C target = pseq_is_empty model.
Proof.
  intros C A target model Hrefines.
  unfold array_pseq_refines in Hrefines.
  destruct (array_is_empty C target) eqn:Hempty;
    destruct (pseq_is_empty model) eqn:Hmodel; try reflexivity.
  - apply array_is_empty_view in Hempty.
    rewrite Hrefines in Hempty.
    apply (proj2 (pseq_is_empty_spec model)) in Hempty.
    rewrite Hempty in Hmodel. discriminate.
  - apply pseq_is_empty_spec in Hmodel.
    rewrite <- Hrefines in Hmodel.
    apply array_is_empty_view in Hmodel.
    rewrite Hmodel in Hempty. discriminate.
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

Lemma array_pseq_length_refines :
  forall (C : array_sequence_contract) A
         (target : array_seq C A) (model : pseq A),
    array_pseq_refines C target model ->
    array_length C target = pseq_length model.
Proof.
  intros C A target model Hrefines.
  unfold array_pseq_refines in Hrefines.
  rewrite array_length_view, pseq_length_view, Hrefines. reflexivity.
Qed.

Lemma array_bucket_get_refines :
  forall (C : array_sequence_contract) K A (eqb : K -> K -> bool) key
         (target : array_seq C (K * A)) (model : pseq (K * A)) index remaining,
    array_pseq_refines C target model ->
    array_bucket_get C eqb key target index remaining =
      native_bucket_get eqb key model index remaining.
Proof.
  intros C K A eqb key target [items] index remaining Hrefines.
  unfold array_pseq_refines in Hrefines.
  rewrite array_bucket_get_view, Hrefines. reflexivity.
Qed.

Lemma array_bucket_set_refines :
  forall (C : array_sequence_contract) K A (eqb : K -> K -> bool) key value
         (target : array_seq C (K * A)) (model : pseq (K * A)) index remaining,
    array_pseq_refines C target model ->
    array_pseq_refines C (array_bucket_set C eqb key value target index remaining)
      (native_bucket_set eqb key value model index remaining).
Proof.
  intros C K A eqb key value target [items] index remaining Hrefines.
  unfold array_pseq_refines in *.
  rewrite array_bucket_set_view, Hrefines. reflexivity.
Qed.

Lemma array_bucket_remove_refines :
  forall (C : array_sequence_contract) K A (eqb : K -> K -> bool) key
         (target : array_seq C (K * A)) (model : pseq (K * A)) index remaining,
    array_pseq_refines C target model ->
    array_pseq_refines C (array_bucket_remove C eqb key target index remaining)
      (native_bucket_remove eqb key model index remaining).
Proof.
  intros C K A eqb key target [items] index remaining Hrefines.
  unfold array_pseq_refines in *.
  rewrite array_bucket_remove_view, Hrefines. reflexivity.
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
