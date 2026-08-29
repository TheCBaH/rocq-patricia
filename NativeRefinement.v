From Stdlib Require Import Lia NArith PArith PeanoNat Strings.String.
Require Import PatriciaBits StringBits.

(** * The representation boundary used by the native extraction

    This file deliberately describes the two changes of representation made by
    [PatriciaExtract.v].  It is not a verification of OCaml's [int], string,
    shift, or unsafe-index primitives; those remain the small foreign runtime
    boundary identified in [patricia.md].  Keeping the conversion functions
    and their elementary laws in Rocq nevertheless makes that boundary
    explicit and gives target refinements a stable statement to prove. *)

(** OCaml values are tagged.  On the supported 64-bit runtime, non-negative
    OCaml [int] values therefore carry 62 payload bits.  We state the bound as
    a strict power-of-two bound rather than materialising [max_int], which is
    the same accepted positive-key domain: [1 .. 2^62 - 1]. *)
Definition native_word_bits : N := 62%N.

Definition fits_native_word (n : N) : Prop :=
  (n < 2 ^ native_word_bits)%N.

Definition native_key (k : PatriciaBits.key) : Prop :=
  fits_native_word (PatriciaBits.word k).

Definition native_mask (mask : N) : Prop :=
  (mask < native_word_bits)%N.

Lemma native_key_word_bound:
  forall k, native_key k ->
    (PatriciaBits.word k < 2 ^ native_word_bits)%N.
Proof.
  exact (fun k H => H).
Qed.

Lemma native_mask_bound:
  forall mask, native_mask mask -> (mask < native_word_bits)%N.
Proof.
  exact (fun mask H => H).
Qed.

(** The source-level bit view has nine logical positions per byte: a
    continuation marker followed by eight character bits.  The native backend
    reserves four low token bits for that tag, so a logical position [9*b+t]
    (where [t < 9]) becomes [16*b+t]. *)
Definition logical_position (byte tag : nat) : nat := 9 * byte + tag.
Definition packed_position (byte tag : nat) : nat := 16 * byte + tag.

Definition encode_position (position : nat) : nat :=
  packed_position (position / 9) (position mod 9).

Definition decode_position (token : nat) : nat :=
  logical_position (token / 16) (token mod 16).

Definition valid_packed_position (token : nat) : Prop :=
  token mod 16 < 9.

Lemma encode_position_byte:
  forall position, encode_position position / 16 = position / 9.
Proof.
  intros position. unfold encode_position, packed_position.
  replace (16 * (position / 9) + position mod 9)
    with ((position / 9) * 16 + position mod 9) by lia.
  rewrite Nat.div_add_l by lia.
  assert (Hsmall : position mod 9 < 16).
  { pose proof (Nat.mod_bound_pos position 9 ltac:(lia) ltac:(lia)); lia. }
  rewrite (Nat.div_small (position mod 9) 16 Hsmall).
  lia.
Qed.

Lemma encode_position_tag:
  forall position, encode_position position mod 16 = position mod 9.
Proof.
  intros position. unfold encode_position, packed_position.
  replace (16 * (position / 9) + position mod 9)
    with (position mod 9 + (position / 9) * 16) by lia.
  rewrite Nat.mod_add by lia.
  assert (Hsmall : position mod 9 < 16).
  { pose proof (Nat.mod_bound_pos position 9 ltac:(lia) ltac:(lia)); lia. }
  rewrite (Nat.mod_small (position mod 9) 16 Hsmall).
  reflexivity.
Qed.

Lemma encode_position_valid:
  forall position, valid_packed_position (encode_position position).
Proof.
  intros position. unfold valid_packed_position.
  rewrite encode_position_tag.
  pose proof (Nat.mod_bound_pos position 9 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma decode_encode_position:
  forall position, decode_position (encode_position position) = position.
Proof.
  intros position. unfold decode_position, logical_position.
  rewrite encode_position_byte, encode_position_tag.
  symmetry. apply Nat.div_mod_eq.
Qed.

Lemma encode_logical_position:
  forall byte tag, tag < 9 ->
    encode_position (logical_position byte tag) = packed_position byte tag.
Proof.
  intros byte tag Htag.
  unfold encode_position, logical_position, packed_position.
  replace (9 * byte + tag) with (byte * 9 + tag) by lia.
  assert (Hdiv : (byte * 9 + tag) / 9 = byte).
  { rewrite Nat.div_add_l by lia. rewrite Nat.div_small by lia. lia. }
  assert (Hmod : (byte * 9 + tag) mod 9 = tag).
  { replace (byte * 9 + tag) with (tag + byte * 9) by lia.
    rewrite Nat.mod_add by lia. rewrite Nat.mod_small by lia. reflexivity. }
  now rewrite Hdiv, Hmod.
Qed.

Lemma packed_position_injective:
  forall byte1 tag1 byte2 tag2,
    tag1 < 9 -> tag2 < 9 ->
    packed_position byte1 tag1 = packed_position byte2 tag2 ->
    byte1 = byte2 /\ tag1 = tag2.
Proof.
  intros byte1 tag1 byte2 tag2 Htag1 Htag2 Heq.
  assert (Hdecode1 : decode_position (packed_position byte1 tag1) =
      logical_position byte1 tag1).
  { rewrite <- (encode_logical_position byte1 tag1 Htag1).
    apply decode_encode_position. }
  assert (Hdecode2 : decode_position (packed_position byte2 tag2) =
      logical_position byte2 tag2).
  { rewrite <- (encode_logical_position byte2 tag2 Htag2).
    apply decode_encode_position. }
  assert (Hlogical : logical_position byte1 tag1 = logical_position byte2 tag2).
  { rewrite <- Hdecode1, <- Hdecode2. now rewrite Heq. }
  pose proof (Nat.div_mod_unique 9 byte1 byte2 tag1 tag2 Htag1 Htag2 Hlogical)
    as [Hbyte Htag].
  split; assumption.
Qed.

Lemma packed_position_byte_order:
  forall byte1 tag1 byte2 tag2,
    tag1 < 9 -> tag2 < 9 -> byte1 < byte2 ->
    packed_position byte1 tag1 < packed_position byte2 tag2.
Proof.
  intros. unfold packed_position. lia.
Qed.

Lemma packed_position_tag_order:
  forall byte tag1 tag2,
    tag1 < tag2 ->
    packed_position byte tag1 < packed_position byte tag2.
Proof.
  intros. unfold packed_position. lia.
Qed.

(** This is the source-level counterpart of the packed native [bit_at]
    realizer.  It performs the same byte/tag decomposition, rejects invalid
    tags, and reads exactly one byte.  [String.get] is deliberately used in
    place of OCaml's unsafe access: proving that primitive correspondence is a
    separate target-language obligation. *)
Definition packed_bit_at (s : string) (token : nat) : bool :=
  let byte := token / 16 in
  let tag := token mod 16 in
  match String.get byte s with
  | None => false
  | Some ch =>
      match tag with
      | 0 => true
      | S offset => if offset <? 8 then StringBits.ascii_bit ch offset else false
      end
  end.

Definition packed_first_diff (left right : string) : option nat :=
  option_map encode_position (StringBits.first_diff left right).

Lemma bit_at_logical_position:
  forall s byte tag,
    tag < 9 ->
    StringBits.bit_at s (logical_position byte tag) =
      match String.get byte s with
      | None => false
      | Some ch =>
          match tag with
          | 0 => true
          | S offset =>
              if offset <? 8 then StringBits.ascii_bit ch offset else false
          end
      end.
Proof.
  induction s as [|head tail IH]; intros byte tag Htag; destruct byte as [|byte].
  - reflexivity.
  - reflexivity.
  - destruct tag as [|tag].
    + change (StringBits.bit_at (String head tail) 0 = true). reflexivity.
    + change (StringBits.bit_at (String head tail) (S tag) =
          if tag <? 8 then StringBits.ascii_bit head tag else false).
      cbn [StringBits.bit_at].
      replace (tag <? 8) with true by (symmetry; apply Nat.ltb_lt; lia).
      reflexivity.
  - cbn [String.get].
    replace (logical_position (S byte) tag)
      with (9 + logical_position byte tag) by (unfold logical_position; lia).
    rewrite StringBits.bit_at_cons_tail.
    apply IH. exact Htag.
Qed.

Lemma packed_bit_at_logical_position:
  forall s byte tag,
    tag < 9 ->
    packed_bit_at s (packed_position byte tag) =
      StringBits.bit_at s (logical_position byte tag).
Proof.
  intros s byte tag Htag.
  unfold packed_bit_at, packed_position.
  assert (Hdiv : (16 * byte + tag) / 16 = byte).
  { replace (16 * byte + tag) with (byte * 16 + tag) by lia.
    rewrite Nat.div_add_l by lia.
    rewrite (Nat.div_small tag 16) by lia. lia. }
  assert (Hmod : (16 * byte + tag) mod 16 = tag).
  { replace (16 * byte + tag) with (tag + byte * 16) by lia.
    rewrite Nat.mod_add by lia.
    rewrite (Nat.mod_small tag 16) by lia. reflexivity. }
  rewrite Hdiv, Hmod.
  symmetry. apply bit_at_logical_position. exact Htag.
Qed.

Lemma packed_bit_at_encode:
  forall s position,
    packed_bit_at s (encode_position position) = StringBits.bit_at s position.
Proof.
  intros s position.
  rewrite <- (decode_encode_position position) at 2.
  unfold decode_position.
  rewrite encode_position_byte, encode_position_tag.
  apply packed_bit_at_logical_position.
  pose proof (Nat.mod_bound_pos position 9 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma packed_first_diff_spec:
  forall left right position,
    packed_first_diff left right = Some (encode_position position) <->
    StringBits.first_diff left right = Some position.
Proof.
  intros left right position.
  unfold packed_first_diff.
  destruct (StringBits.first_diff left right) as [d|] eqn:H; cbn.
  - split; intro E.
    + injection E as E.
      change (encode_position d = encode_position position) in E.
      apply (f_equal decode_position) in E.
      rewrite !decode_encode_position in E.
      now rewrite E.
    + injection E as E. subst position. reflexivity.
  - split; discriminate.
Qed.

Lemma packed_first_diff_valid:
  forall left right token,
    packed_first_diff left right = Some token -> valid_packed_position token.
Proof.
  intros left right token H.
  unfold packed_first_diff in H.
  destruct (StringBits.first_diff left right) as [position|] eqn:E;
    cbn in H; try discriminate.
  injection H as H. subst token. apply encode_position_valid.
Qed.
