(** Source-defined scalar boundary for the native HAMT extraction.

    These definitions remain transparently equal to [HashTableBits], so the
    existing logical model and proofs continue to state facts over unbounded
    [N].  The selected extraction binds only these names to OCaml operations.
    Public routing establishes the 30-bit hash, six-level, 32-bit bitmap and
    slot bounds recorded in the performance plan; target execution of those
    bounds is an explicit foreign obligation. *)

From Stdlib Require Import NArith.
Require Import HashTableBits.

Definition native_chunk (full_hash : N) (depth : nat) : N :=
  chunk full_hash depth.

Definition native_bitmap_bit (slot : N) : N := bitmap_bit slot.

Definition native_bitmap_has (bitmap slot : N) : bool :=
  bitmap_has bitmap slot.

Definition native_rank (bitmap slot : N) : nat := rank bitmap slot.

Definition native_bitmap_insert (bitmap slot : N) : N :=
  N.lor bitmap (bitmap_bit slot).

Definition native_bitmap_remove (bitmap slot : N) : N :=
  N.ldiff bitmap (bitmap_bit slot).

Lemma native_chunk_eq : forall full_hash depth,
  native_chunk full_hash depth = chunk full_hash depth.
Proof. reflexivity. Qed.

Lemma native_bitmap_bit_eq : forall slot,
  native_bitmap_bit slot = bitmap_bit slot.
Proof. reflexivity. Qed.

Lemma native_bitmap_has_eq : forall bitmap slot,
  native_bitmap_has bitmap slot = bitmap_has bitmap slot.
Proof. reflexivity. Qed.

Lemma native_rank_eq : forall bitmap slot,
  native_rank bitmap slot = rank bitmap slot.
Proof. reflexivity. Qed.

Lemma native_bitmap_insert_eq : forall bitmap slot,
  native_bitmap_insert bitmap slot = N.lor bitmap (bitmap_bit slot).
Proof. reflexivity. Qed.

Lemma native_bitmap_remove_eq : forall bitmap slot,
  native_bitmap_remove bitmap slot = N.ldiff bitmap (bitmap_bit slot).
Proof. reflexivity. Qed.
