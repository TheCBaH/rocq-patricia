(** Fixed-width routing and dense-child primitives for the 32-way HAMT.

    Hashes have six five-bit chunks; bitmaps are deliberately modelled as
    independent 32-bit [N] values.  The executable source uses a bounded
    popcount worker so no target machine-width assumption is hidden here. *)

From Stdlib Require Import Arith Bool Lia List NArith.
Import ListNotations.

Require Import HashTableSpec.

Set Implicit Arguments.

Definition branch_width : N := 32%N.
Definition branch_mask : N := 31%N.
Definition branch_levels : nat := 6.
Definition bitmap_limit : N := 4294967296%N. (* 2^32 *)
Definition full_bitmap : N := 4294967295%N.  (* 2^32 - 1 *)

Definition chunk (full_hash : N) (depth : nat) : N :=
  N.land (N.shiftr full_hash (N.of_nat (5 * depth))) branch_mask.

Definition bitmap_bit (slot : N) : N := N.shiftl 1 slot.
Definition bitmap_has (bitmap slot : N) : bool :=
  negb (N.eqb (N.land bitmap (bitmap_bit slot)) 0).

Fixpoint popcount_worker (fuel : nat) (word : N) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      (if N.even word then O else S O) + popcount_worker fuel' (N.shiftr word 1)
  end.

Definition popcount32 (bitmap : N) : nat := popcount_worker 32 bitmap.

Definition rank (bitmap slot : N) : nat :=
  popcount32 (N.land bitmap (N.ones slot)).

Fixpoint occupied_slots_from (fuel : nat) (bitmap slot : N) : list N :=
  match fuel with
  | O => []
  | S fuel' =>
      if bitmap_has bitmap slot
      then slot :: occupied_slots_from fuel' bitmap (N.succ slot)
      else occupied_slots_from fuel' bitmap (N.succ slot)
  end.

Definition occupied_slots (bitmap : N) : list N :=
  occupied_slots_from 32 bitmap 0.

Lemma chunk_bound :
  forall full_hash depth, (chunk full_hash depth < branch_width)%N.
Proof.
  intros. unfold chunk, branch_mask, branch_width.
  pose proof (N.land_le_r (N.shiftr full_hash (N.of_nat (5 * depth))) 31) as H.
  lia.
Qed.

Lemma chunk_zero : forall full_hash, chunk full_hash 0 = N.land full_hash branch_mask.
Proof. intros. reflexivity. Qed.

Lemma bitmap_bit_zero : bitmap_bit 0 = 1%N.
Proof. reflexivity. Qed.

Lemma bitmap_bit_31 : bitmap_bit 31 = 2147483648%N.
Proof. now vm_compute. Qed.

Lemma full_bitmap_bound : (full_bitmap < bitmap_limit)%N.
Proof. now vm_compute. Qed.

Lemma popcount_worker_zero : forall fuel, popcount_worker fuel 0 = 0.
Proof.
  induction fuel; simpl; auto.
Qed.

Lemma popcount_worker_bound :
  forall fuel word, popcount_worker fuel word <= fuel.
Proof.
  induction fuel as [|fuel IH]; intros word; simpl; auto with arith.
  destruct (N.even word) eqn:Heven; simpl.
  - change (popcount_worker fuel (N.shiftr word 1) <= S fuel).
    eapply Nat.le_trans; [apply IH|lia].
  - change (S (popcount_worker fuel (N.shiftr word 1)) <= S fuel).
    now apply le_n_S, IH.
Qed.

Lemma popcount32_bound : forall bitmap, popcount32 bitmap <= 32.
Proof. intros. unfold popcount32. apply popcount_worker_bound. Qed.

Lemma rank_bound : forall bitmap slot, rank bitmap slot <= 32.
Proof. intros. unfold rank. apply popcount32_bound. Qed.

Lemma rank_empty : forall slot, rank 0 slot = 0.
Proof. intros. unfold rank, popcount32. now rewrite N.land_0_l, popcount_worker_zero. Qed.

Lemma rank_slot_zero : forall bitmap, rank bitmap 0 = 0.
Proof. intros. unfold rank, popcount32. now rewrite N.ones_0, N.land_0_r, popcount_worker_zero. Qed.

Lemma full_bitmap_has_slot_31 : bitmap_has full_bitmap 31 = true.
Proof. now vm_compute. Qed.

Lemma full_bitmap_popcount : popcount32 full_bitmap = 32.
Proof. now vm_compute. Qed.

Lemma full_bitmap_rank_slot_31 : rank full_bitmap 31 = 31.
Proof. now vm_compute. Qed.

Lemma full_bitmap_occupied_slots :
  occupied_slots full_bitmap = map N.of_nat (List.seq 0 32).
Proof. now vm_compute. Qed.

Definition dense_get {A : Type} (index : nat) (children : list A) : option A :=
  nth_error children index.

Fixpoint dense_insert {A : Type} (index : nat) (child : A) (children : list A)
    : list A :=
  match index, children with
  | O, _ => child :: children
  | S index', [] => [child]
  | S index', head :: tail => head :: dense_insert index' child tail
  end.

Fixpoint dense_replace {A : Type} (index : nat) (child : A) (children : list A)
    : list A :=
  match index, children with
  | O, [] => []
  | O, _ :: tail => child :: tail
  | S index', [] => []
  | S index', head :: tail => head :: dense_replace index' child tail
  end.

Fixpoint dense_remove {A : Type} (index : nat) (children : list A) : list A :=
  match index, children with
  | O, [] => []
  | O, _ :: tail => tail
  | S index', [] => []
  | S index', head :: tail => head :: dense_remove index' tail
  end.

Lemma dense_insert_length :
  forall A index (child : A) children,
    length (dense_insert index child children) = S (length children).
Proof.
  intros A index. induction index as [|index IH]; intros child children;
    destruct children as [|head tail]; simpl; auto.
Qed.

Lemma dense_replace_length :
  forall A index (child : A) children,
    length (dense_replace index child children) = length children.
Proof.
  intros A index. induction index as [|index IH]; intros child children;
    destruct children as [|head tail]; simpl; auto.
Qed.

Lemma dense_remove_length_le :
  forall A index (children : list A),
    length (dense_remove index children) <= length children.
Proof.
  intros A index. induction index as [|index IH]; intros children;
    destruct children as [|head tail]; simpl; auto with arith.
Qed.

Lemma dense_insert_empty :
  forall A (child : A) index, dense_insert index child [] = [child].
Proof. intros A child [|index]; reflexivity. Qed.

Lemma dense_get_insert_same :
  forall A index (child : A) children,
    index <= length children ->
    dense_get index (dense_insert index child children) = Some child.
Proof.
  intros A index. induction index as [|index IH]; intros child children Hbound.
  - destruct children; reflexivity.
  - destruct children as [|head tail]; simpl in Hbound.
    + lia.
    + simpl. unfold dense_get in IH. apply IH. lia.
Qed.

Lemma dense_get_replace_same :
  forall A index (child : A) children,
    index < length children ->
    dense_get index (dense_replace index child children) = Some child.
Proof.
  intros A index. induction index as [|index IH]; intros child children Hbound.
  - destruct children; simpl in Hbound; try lia. reflexivity.
  - destruct children as [|head tail]; simpl in Hbound.
    + lia.
    + simpl. unfold dense_get in IH. apply IH. lia.
Qed.
