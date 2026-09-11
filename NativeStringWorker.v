From Stdlib Require Import Bool Lia PeanoNat Strings.Ascii Strings.String.
Require Import NativeRefinement StringBits.

(** Source-defined workers used by the native packed-string binding.

    The definitions below intentionally separate the executable control flow
    from the three target primitives realized in [PatriciaExtract.v].  Their
    source meanings are ordinary Rocq definitions; the enclosing guard is the
    proof-side justification for the target unsafe read. *)

Definition native_token_byte (token : nat) : nat := token / 16.
Definition native_token_tag (token : nat) : nat := token mod 16.
Definition native_length (s : string) : nat := String.length s.
Definition native_lt (left right : nat) : bool := left <? right.
Definition native_tag_is_marker (tag : nat) : bool := tag =? 0.
Definition native_tag_is_data (tag : nat) : bool := tag <=? 8.
Definition native_tag_offset (tag : nat) : nat := tag - 1.

Definition native_unsafe_get (s : string) (byte : nat) : Ascii.ascii :=
  match String.get byte s with
  | Some ch => ch
  | None => Ascii.zero
  end.

Definition native_code_bit (ch : Ascii.ascii) (offset : nat) : bool :=
  StringBits.ascii_bit ch offset.

(** One guarded indexed read, with the native packed tag convention.  The
    branch order is part of the contract: no byte is consumed unless the
    index is in range, and invalid tags produce [false]. *)
Definition packed_bit_at (s : string) (token : nat) : bool :=
  let byte := native_token_byte token in
  let tag := native_token_tag token in
  if native_lt byte (native_length s) then
    if native_tag_is_marker tag then true
    else if native_tag_is_data tag then
      native_code_bit (native_unsafe_get s byte) (native_tag_offset tag)
    else false
  else false.

Lemma native_unsafe_get_correct:
  forall s byte,
    native_unsafe_get s byte =
      match String.get byte s with Some ch => ch | None => Ascii.zero end.
Proof. reflexivity. Qed.

Theorem packed_bit_at_refines_model:
  forall s token,
    packed_bit_at s token = NativeRefinement.packed_bit_at s token.
Proof.
  intros s token.
  unfold packed_bit_at, NativeRefinement.packed_bit_at,
    native_token_byte, native_token_tag, native_length, native_lt,
    native_tag_is_marker, native_tag_is_data, native_tag_offset,
    native_code_bit.
  destruct (token / 16 <? String.length s) eqn:Hbound.
  - pose proof (proj1 (Nat.ltb_lt _ _) Hbound) as Hlt.
    destruct (NativeRefinement.string_get_in_bounds s (token / 16) Hlt)
      as [ch Hget].
    rewrite Hget.
    destruct (token mod 16) as [|offset]; [reflexivity|].
    destruct offset as [|offset].
    + unfold native_unsafe_get. now rewrite Hget.
    + destruct (S (S offset) <=? 8) eqn:Hdata;
        destruct (S offset <? 8) eqn:Hoffset.
      * unfold native_unsafe_get. now rewrite Hget.
      * apply Nat.leb_le in Hdata. apply Nat.ltb_ge in Hoffset. lia.
      * apply Nat.leb_gt in Hdata. apply Nat.ltb_lt in Hoffset. lia.
      * reflexivity.
  - pose proof (proj1 (Nat.ltb_ge _ _) Hbound) as Hge.
    now rewrite NativeRefinement.string_get_past_end by exact Hge.
Qed.

Theorem packed_bit_at_encode_refines:
  forall s position,
    packed_bit_at s (NativeRefinement.encode_position position) =
      StringBits.bit_at s position.
Proof.
  intros s position.
  rewrite packed_bit_at_refines_model.
  apply NativeRefinement.packed_bit_at_encode.
Qed.

Corollary packed_bit_at_refines_representation:
  forall s bytes token,
    NativeRefinement.native_string_refines s bytes ->
    packed_bit_at s token =
      NativeRefinement.native_packed_bit_at bytes token.
Proof.
  intros s bytes token Hrefines.
  rewrite packed_bit_at_refines_model.
  symmetry. now apply NativeRefinement.native_packed_bit_at_refines_representation.
Qed.
