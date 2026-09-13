(** Source model for the future compact-array backend.

    [pseq] intentionally exposes only a logical list view in Rocq.  H4's
    target array adapter must refine these operations by allocating a fresh
    private array for every update; it is not yet an OCaml heap proof. *)

From Stdlib Require Import List NArith.
Import ListNotations.

Require Import HashTable HashTableBits.

Set Implicit Arguments.

Record pseq (A : Type) : Type := {
  pseq_view : list A
}.

Arguments pseq_view {A} _.

Definition pseq_empty {A : Type} : pseq A := {| pseq_view := [] |}.
Definition pseq_of_list {A : Type} (items : list A) : pseq A :=
  {| pseq_view := items |}.
Definition pseq_get {A : Type} (index : nat) (items : pseq A) : option A :=
  nth_error (pseq_view items) index.
Definition pseq_insert {A : Type} (index : nat) (item : A) (items : pseq A)
    : pseq A :=
  pseq_of_list (dense_insert index item (pseq_view items)).
Definition pseq_replace {A : Type} (index : nat) (item : A) (items : pseq A)
    : pseq A :=
  pseq_of_list (dense_replace index item (pseq_view items)).
Definition pseq_remove {A : Type} (index : nat) (items : pseq A) : pseq A :=
  pseq_of_list (dense_remove index (pseq_view items)).

Lemma pseq_empty_view :
  forall A, @pseq_view A pseq_empty = [].
Proof. reflexivity. Qed.

Lemma pseq_get_view :
  forall A index (items : pseq A),
    pseq_get index items = nth_error (pseq_view items) index.
Proof. reflexivity. Qed.

Lemma pseq_insert_view :
  forall A index (item : A) items,
    pseq_view (pseq_insert index item items) =
    dense_insert index item (pseq_view items).
Proof. reflexivity. Qed.

Lemma pseq_replace_view :
  forall A index (item : A) items,
    pseq_view (pseq_replace index item items) =
    dense_replace index item (pseq_view items).
Proof. reflexivity. Qed.

Lemma pseq_remove_view :
  forall A index (items : pseq A),
    pseq_view (pseq_remove index items) = dense_remove index (pseq_view items).
Proof. reflexivity. Qed.

Inductive native_tree (K A : Type) : Type :=
| NativeEmpty
| NativeLeaf (full_hash : N) (key : K) (value : A)
| NativeCollision (full_hash : N) (entries : pseq (K * A))
| NativeBranch (bitmap : N) (children : pseq (native_tree K A)).

Arguments NativeEmpty {K A}.
Arguments NativeLeaf {K A} _ _ _.
Arguments NativeCollision {K A} _ _.
Arguments NativeBranch {K A} _ _.

Fixpoint source_of_native {K A : Type} (native : native_tree K A) : tree K A :=
  match native with
  | NativeEmpty => Empty
  | NativeLeaf full_hash key value => Leaf full_hash key value
  | NativeCollision full_hash entries => Collision full_hash (pseq_view entries)
  | NativeBranch bitmap children =>
      Branch bitmap (map source_of_native (pseq_view children))
  end.

Definition native_refines {K A : Type} (native : native_tree K A)
    (source : tree K A) : Prop := source_of_native native = source.

Lemma native_empty_refines :
  forall K A, @native_refines K A NativeEmpty Empty.
Proof. reflexivity. Qed.

Lemma native_leaf_refines :
  forall K A full_hash (key : K) (value : A),
    native_refines (NativeLeaf full_hash key value) (Leaf full_hash key value).
Proof. reflexivity. Qed.

Lemma native_collision_refines :
  forall K A full_hash (entries : list (K * A)),
    native_refines (NativeCollision full_hash (pseq_of_list entries))
                   (Collision full_hash entries).
Proof. reflexivity. Qed.
