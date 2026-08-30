From Stdlib Require Import Lia NArith PArith PeanoNat Lists.List Strings.Ascii Strings.String.
Require Import PatriciaBits StringBits.

Import ListNotations.

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

(** ** Bounded integer routing model

    The integer extraction represents a source [positive] by the identical
    non-negative OCaml payload and implements the following operations with
    [lsr], [land], [lxor], and a small [log2] loop.  We state their meaning
    over bounded unsigned payloads here.  This is intentionally separate from
    the foreign-function obligation that the OCaml operators implement these
    mathematical operations; the theorems below make that remaining
    obligation pointwise and finite-domain. *)
Definition native_prefix_word (key mask : N) : N :=
  N.shiftr key (N.succ mask).

Definition native_matches_prefix (key prefix mask : N) : bool :=
  N.eqb (native_prefix_word key mask) prefix.

Definition native_zero_bit (key mask : N) : bool :=
  negb (N.testbit key mask).

Definition native_highest_differing_bit (left right : N) : N :=
  N.log2 (N.lxor left right).

Definition native_mask_above (left right : N) : bool := N.ltb right left.

Lemma native_prefix_word_refines:
  forall key mask,
    native_prefix_word (PatriciaBits.word key) mask =
      PatriciaBits.prefix key mask.
Proof.
  reflexivity.
Qed.

Lemma native_matches_prefix_refines:
  forall key prefix mask,
    native_matches_prefix (PatriciaBits.word key) prefix mask =
      PatriciaBits.matches_prefix key prefix mask.
Proof.
  reflexivity.
Qed.

Lemma native_zero_bit_refines:
  forall key mask,
    native_zero_bit (PatriciaBits.word key) mask =
      PatriciaBits.zero_bit key mask.
Proof.
  reflexivity.
Qed.

Lemma native_highest_differing_bit_refines:
  forall left right,
    native_highest_differing_bit (PatriciaBits.word left)
      (PatriciaBits.word right) =
      PatriciaBits.highest_differing_bit left right.
Proof.
  reflexivity.
Qed.

Lemma native_mask_above_refines:
  forall left right,
    native_mask_above left right = PatriciaBits.mask_above left right.
Proof.
  reflexivity.
Qed.

(** Every result which the routing code retains as a word remains in the
    payload domain.  The split-bit result is instead a mask, and is bounded by
    the word width even for the unused equal-key case ([log2 0 = 0]). *)
Lemma native_prefix_word_fits:
  forall key mask,
    fits_native_word key -> fits_native_word (native_prefix_word key mask).
Proof.
  intros key mask Hkey. unfold fits_native_word, native_prefix_word in *.
  eapply N.le_lt_trans; [apply N.shiftr_upper_bound|exact Hkey].
Qed.

Lemma native_log2_fits_mask:
  forall key,
    fits_native_word key -> key <> 0%N ->
      (N.log2 key < native_word_bits)%N.
Proof.
  intros key Hfits Hnonzero. unfold fits_native_word in Hfits.
  apply (proj1 (N.log2_lt_pow2 key native_word_bits
    (proj1 (N.neq_0_lt_0 key) Hnonzero))).
  exact Hfits.
Qed.

Lemma native_highest_differing_bit_fits_mask:
  forall left right,
    fits_native_word left -> fits_native_word right ->
    native_mask (native_highest_differing_bit left right).
Proof.
  intros left right Hleft Hright.
  unfold native_mask, native_highest_differing_bit.
  apply N.nle_gt. intro Hwidth.
  assert (Hleft_bit : N.testbit left (N.log2 (N.lxor left right)) = false).
  { destruct left as [|left].
    - reflexivity.
    - apply N.bits_above_log2.
      eapply N.lt_le_trans.
      + apply native_log2_fits_mask.
        * exact Hleft.
        * discriminate.
      + exact Hwidth. }
  assert (Hright_bit : N.testbit right (N.log2 (N.lxor left right)) = false).
  { destruct right as [|right].
    - reflexivity.
    - apply N.bits_above_log2.
      eapply N.lt_le_trans.
      + apply native_log2_fits_mask.
        * exact Hright.
        * discriminate.
      + exact Hwidth. }
  destruct (N.eq_dec (N.lxor left right) 0%N) as [Hzero|Hnonzero].
  - rewrite Hzero in Hwidth. change (62 <= 0)%N in Hwidth. lia.
  - pose proof (N.bit_log2 (N.lxor left right) Hnonzero) as Hbit.
    rewrite N.lxor_spec, Hleft_bit, Hright_bit in Hbit.
    discriminate.
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
  rewrite Nat.Div0.mod_add.
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
    rewrite Nat.Div0.mod_add. rewrite Nat.mod_small by lia. reflexivity. }
  now rewrite Hdiv, Hmod.
Qed.

Lemma encode_decode_position:
  forall token, valid_packed_position token ->
    encode_position (decode_position token) = token.
Proof.
  intros token Hvalid.
  unfold decode_position.
  rewrite encode_logical_position by exact Hvalid.
  unfold packed_position.
  symmetry. apply Nat.div_mod_eq.
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

(** Safe logical indexing is the source counterpart of the native string
    runtime.  These facts will also discharge every [unsafe_get] guard. *)
Lemma string_get_past_end:
  forall s byte, String.length s <= byte -> String.get byte s = None.
Proof.
  induction s as [|ch rest IH]; intros byte Hbound.
  - reflexivity.
  - destruct byte as [|byte].
    + cbn in Hbound. lia.
    + cbn [String.get]. apply IH. cbn in Hbound. lia.
Qed.

Lemma string_get_in_bounds:
  forall s byte, byte < String.length s ->
    exists ch, String.get byte s = Some ch.
Proof.
  induction s as [|ch rest IH]; intros byte Hbound.
  - cbn in Hbound. lia.
  - destruct byte as [|byte].
    + exists ch. reflexivity.
    + cbn [String.get]. apply IH. cbn in Hbound. lia.
Qed.

(** ** Native byte strings and guarded access

    The native-string extraction maps a Rocq string to an OCaml byte string.
    The following finite model makes that mapping concrete: a native string is
    a list of the unsigned byte codes returned by [Char.code].  The equality
    [native_bytes s] is the foreign-interface contract for the representation
    of [s]; the lemmas below prove everything that follows once an OCaml value
    satisfies that contract. *)
Fixpoint native_bytes (s : string) : list N :=
  match s with
  | EmptyString => []
  | String ch tail => Ascii.N_of_ascii ch :: native_bytes tail
  end.

Definition native_byte_length (bytes : list N) : nat := List.length bytes.

Definition native_byte_get (bytes : list N) (byte : nat) : option N :=
  nth_error bytes byte.

(** This models [String.unsafe_get] after [Char.code].  Its arbitrary
    out-of-range default is intentionally unobservable: every consumer below
    proves an in-range guard before using it. *)
Definition native_unsafe_byte_code (bytes : list N) (byte : nat) : N :=
  nth byte bytes 0%N.

Definition native_string_refines (s : string) (bytes : list N) : Prop :=
  bytes = native_bytes s.

Lemma native_bytes_length:
  forall s, native_byte_length (native_bytes s) = String.length s.
Proof.
  induction s as [|ch tail IH].
  - reflexivity.
  - change (S (List.length (native_bytes tail)) = S (String.length tail)).
    unfold native_byte_length in IH. now rewrite IH.
Qed.

Lemma native_bytes_get:
  forall s byte,
    native_byte_get (native_bytes s) byte =
      option_map Ascii.N_of_ascii (String.get byte s).
Proof.
  induction s as [|ch tail IH]; intros [|byte]; cbn; auto.
Qed.

Lemma native_bytes_unsafe_byte_code:
  forall s byte ch,
    String.get byte s = Some ch ->
    native_unsafe_byte_code (native_bytes s) byte = Ascii.N_of_ascii ch.
Proof.
  intros s byte ch Hget. unfold native_unsafe_byte_code.
  apply (nth_error_nth (native_bytes s) byte 0%N).
  unfold native_byte_get. rewrite native_bytes_get, Hget. reflexivity.
Qed.

Lemma native_bytes_unsafe_byte_code_guarded:
  forall s byte,
    byte < native_byte_length (native_bytes s) ->
    exists code,
      native_byte_get (native_bytes s) byte = Some code /\
      native_unsafe_byte_code (native_bytes s) byte = code.
Proof.
  intros s byte Hbound.
  rewrite native_bytes_length in Hbound.
  destruct (string_get_in_bounds s byte Hbound) as [ch Hget].
  exists (Ascii.N_of_ascii ch). split.
  - unfold native_byte_get. rewrite native_bytes_get, Hget. reflexivity.
  - now apply native_bytes_unsafe_byte_code.
Qed.

(** The [Char.code] result is always an unsigned byte. *)
Lemma native_bytes_code_bound:
  forall s byte code,
    native_byte_get (native_bytes s) byte = Some code -> (code < 256)%N.
Proof.
  intros s byte code Hget.
  rewrite native_bytes_get in Hget.
  destruct (String.get byte s) as [ch|] eqn:Hsource; cbn in Hget;
    try discriminate.
  injection Hget as Hcode. subst code.
  apply Ascii.N_ascii_bounded.
Qed.

(** These are the three index facts needed by the handwritten string
    realizers.  They correspond respectively to [bit_at], the body of the
    [first_diff] scan, and the two reads in the final-byte case of the bounded
    prefix scan. *)
Definition common_byte_length (left right : string) : nat :=
  Nat.min (String.length left) (String.length right).

Lemma bit_at_unsafe_get_guard:
  forall s byte,
    byte < String.length s ->
    byte < native_byte_length (native_bytes s).
Proof.
  intros s byte Hbound. now rewrite native_bytes_length.
Qed.

Lemma first_diff_unsafe_get_guard:
  forall left right byte,
    byte < common_byte_length left right ->
    byte < String.length left /\ byte < String.length right.
Proof.
  intros left right byte Hbound. unfold common_byte_length in Hbound.
  split.
  - eapply Nat.lt_le_trans; [exact Hbound|apply Nat.le_min_l].
  - eapply Nat.lt_le_trans; [exact Hbound|apply Nat.le_min_r].
Qed.

Lemma bounded_prefix_scan_unsafe_get_guard:
  forall left right byte,
    byte <= common_byte_length left right ->
    byte <> common_byte_length left right ->
    byte < String.length left /\ byte < String.length right.
Proof.
  intros left right byte Hle Hneq.
  assert (Hlt : byte < common_byte_length left right) by lia.
  now apply first_diff_unsafe_get_guard.
Qed.

Lemma bounded_prefix_final_unsafe_get_guard:
  forall left right byte,
    (byte <? String.length left) = true ->
    (byte <? String.length right) = true ->
    byte < String.length left /\ byte < String.length right.
Proof.
  intros left right byte Hleft Hright.
  now apply Nat.ltb_lt in Hleft, Hright.
Qed.

(** This is the source-level counterpart of the packed native [bit_at]
    realizer.  It performs the same byte/tag decomposition, rejects invalid
    tags, and reads exactly one byte.  [String.get] is deliberately used in
    place of OCaml's unsafe access: the guarded native model immediately above
    is the precise foreign-interface contract for that replacement. *)
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

Lemma packed_bit_at_past_end:
  forall s token, String.length s <= token / 16 ->
    packed_bit_at s token = false.
Proof.
  intros s token Hbound. unfold packed_bit_at.
  rewrite string_get_past_end by exact Hbound. reflexivity.
Qed.

Lemma packed_bit_at_invalid_tag:
  forall s token, 9 <= token mod 16 -> packed_bit_at s token = false.
Proof.
  intros s token Htag. unfold packed_bit_at.
  destruct (String.get (token / 16) s) as [ch|] eqn:Hget; [|reflexivity].
  destruct (token mod 16) as [|offset].
  - lia.
  - replace (offset <? 8) with false by
      (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
Qed.

(** At a byte which is already known to differ, the native scanner obtains
    the first differing character bit from an XOR and its leading zeroes.
    This safe source-level worker expresses precisely that choice by walking
    the eight most-significant-first bits.  The target arithmetic used for
    XOR and leading-zeroes is still a separate refinement obligation. *)
Fixpoint ascii_first_diff_from
    (fuel offset : nat) (left right : Ascii.ascii) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if Bool.eqb (StringBits.ascii_bit left offset)
          (StringBits.ascii_bit right offset)
      then ascii_first_diff_from fuel' (S offset) left right
      else Some offset
  end.

Definition ascii_first_diff (left right : Ascii.ascii) : option nat :=
  ascii_first_diff_from 8 0 left right.

Lemma ascii_first_diff_from_none:
  forall fuel offset left right,
    ascii_first_diff_from fuel offset left right = None <->
    forall n, offset <= n < offset + fuel ->
      StringBits.ascii_bit left n = StringBits.ascii_bit right n.
Proof.
  induction fuel as [|fuel IH]; intros offset left right; cbn.
  - split; intros; [lia | reflexivity].
  - destruct (Bool.eqb (StringBits.ascii_bit left offset)
      (StringBits.ascii_bit right offset)) eqn:E.
    + apply Bool.eqb_prop in E. rewrite IH. split.
      * intros H n Hrange. destruct (Nat.eq_dec n offset) as [->|Hneq].
        -- exact E.
        -- apply H. lia.
      * intros H n Hrange. apply H. lia.
    + split.
      * discriminate.
      * intros H. exfalso. apply (proj1 (Bool.eqb_false_iff _ _) E).
        apply H. lia.
Qed.

Lemma ascii_first_diff_from_some:
  forall fuel offset left right differing,
    ascii_first_diff_from fuel offset left right = Some differing ->
    offset <= differing < offset + fuel /\
    StringBits.ascii_bit left differing <>
      StringBits.ascii_bit right differing /\
    (forall n, offset <= n < differing ->
      StringBits.ascii_bit left n = StringBits.ascii_bit right n).
Proof.
  induction fuel as [|fuel IH]; intros offset left right differing H; cbn in H.
  - discriminate.
  - destruct (Bool.eqb (StringBits.ascii_bit left offset)
      (StringBits.ascii_bit right offset)) eqn:E.
    + apply Bool.eqb_prop in E.
      specialize (IH (S offset) left right differing H).
      destruct IH as [Hrange [Hdiff Hbefore]].
      split; [lia|]. split; [assumption|]. intros n Hn.
      destruct (Nat.eq_dec n offset) as [->|Hneq]; [exact E|].
      apply Hbefore. lia.
    + inversion H; subst differing.
      split; [lia|]. split; [apply (proj1 (Bool.eqb_false_iff _ _) E)|].
      intros; lia.
Qed.

Lemma ascii_first_diff_unequal_exists:
  forall left right,
    left <> right -> exists differing, ascii_first_diff left right = Some differing.
Proof.
  intros left right Hneq. unfold ascii_first_diff.
  destruct (ascii_first_diff_from 8 0 left right) as [differing|] eqn:H.
  - eauto.
  - exfalso. apply Hneq. apply StringBits.ascii_bit_ext. intros n Hn.
    apply (proj1 (ascii_first_diff_from_none 8 0 left right) H).
    lia.
Qed.

Lemma ascii_first_diff_characterization:
  forall left right differing,
    StringBits.ascii_bit left differing <>
      StringBits.ascii_bit right differing ->
    (forall n, n < differing ->
      StringBits.ascii_bit left n = StringBits.ascii_bit right n) ->
    ascii_first_diff left right = Some differing.
Proof.
  intros left right differing Hdiff Hbefore.
  destruct (ascii_first_diff left right) as [first|] eqn:Hfirst.
  - destruct (ascii_first_diff_from_some 8 0 left right first Hfirst)
      as [Hrange [Hfirstdiff Hfirstbefore]].
    destruct (Nat.lt_trichotomy differing first) as [Hlt | [Heq | Hgt]].
    + exfalso. apply Hdiff. apply Hfirstbefore. lia.
    + subst first. reflexivity.
    + exfalso. apply Hfirstdiff. apply Hbefore. exact Hgt.
  - pose proof (proj1 (ascii_first_diff_from_none 8 0 left right) Hfirst)
      as Hall.
    assert (Heq : left = right).
    { apply StringBits.ascii_bit_ext. intros n Hn. apply Hall. lia. }
    subst right. exfalso. apply Hdiff. reflexivity.
Qed.

(** Boolean-XOR model of the differing-byte calculation performed by the
    extracted worker.  The character constructor stores bits least
    significant first, whereas [ascii_bit] exposes them most significant
    first; [ascii_xor_bit] below connects those two views. *)
Definition ascii_xor (left right : Ascii.ascii) : Ascii.ascii :=
  match left, right with
  | Ascii.Ascii l0 l1 l2 l3 l4 l5 l6 l7,
    Ascii.Ascii r0 r1 r2 r3 r4 r5 r6 r7 =>
      Ascii.Ascii (xorb l0 r0) (xorb l1 r1) (xorb l2 r2) (xorb l3 r3)
        (xorb l4 r4) (xorb l5 r5) (xorb l6 r6) (xorb l7 r7)
  end.

Fixpoint ascii_leading_zeroes_from
    (fuel offset : nat) (difference : Ascii.ascii) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if StringBits.ascii_bit difference offset
      then Some offset
      else ascii_leading_zeroes_from fuel' (S offset) difference
  end.

Definition ascii_leading_zeroes (difference : Ascii.ascii) : option nat :=
  ascii_leading_zeroes_from 8 0 difference.

Definition xor_first_diff (left right : Ascii.ascii) : option nat :=
  if Ascii.eqb left right then None else ascii_leading_zeroes (ascii_xor left right).

Lemma ascii_xor_bit:
  forall left right n, n < 8 ->
    StringBits.ascii_bit (ascii_xor left right) n =
      xorb (StringBits.ascii_bit left n) (StringBits.ascii_bit right n).
Proof.
  intros [l0 l1 l2 l3 l4 l5 l6 l7]
         [r0 r1 r2 r3 r4 r5 r6 r7] n Hn.
  destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; cbn; try reflexivity; lia.
Qed.

Lemma ascii_xor_zero_iff:
  forall left right, ascii_xor left right = Ascii.zero <-> left = right.
Proof.
  intros left right. split.
  - intro Hzero. apply StringBits.ascii_bit_ext. intros n Hn.
    assert (Hbit : StringBits.ascii_bit (ascii_xor left right) n = false).
    { rewrite Hzero. destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; reflexivity. }
    rewrite ascii_xor_bit in Hbit by exact Hn.
    destruct (StringBits.ascii_bit left n), (StringBits.ascii_bit right n);
      cbn in Hbit; try discriminate; reflexivity.
  - intros ->. destruct right as [r0 r1 r2 r3 r4 r5 r6 r7].
    cbn. repeat rewrite Bool.xorb_nilpotent. reflexivity.
Qed.

Lemma ascii_leading_zeroes_from_none:
  forall fuel offset difference,
    ascii_leading_zeroes_from fuel offset difference = None <->
    forall n, offset <= n < offset + fuel ->
      StringBits.ascii_bit difference n = false.
Proof.
  induction fuel as [|fuel IH]; intros offset difference; cbn.
  - split; intros; [lia | reflexivity].
  - destruct (StringBits.ascii_bit difference offset) eqn:E.
    + split.
      * discriminate.
      * intros H. specialize (H offset ltac:(lia)). rewrite E in H. discriminate.
    + rewrite IH. split.
      * intros H n Hrange. destruct (Nat.eq_dec n offset) as [->|Hneq].
        -- exact E.
        -- apply H. lia.
      * intros H n Hrange. apply H. lia.
Qed.

Lemma ascii_leading_zeroes_from_some:
  forall fuel offset difference differing,
    ascii_leading_zeroes_from fuel offset difference = Some differing ->
    offset <= differing < offset + fuel /\
    StringBits.ascii_bit difference differing = true /\
    (forall n, offset <= n < differing ->
      StringBits.ascii_bit difference n = false).
Proof.
  induction fuel as [|fuel IH]; intros offset difference differing H; cbn in H.
  - discriminate.
  - destruct (StringBits.ascii_bit difference offset) eqn:E.
    + inversion H; subst differing. split; [lia|]. split; [exact E|]. intros; lia.
    + specialize (IH (S offset) difference differing H).
      destruct IH as [Hrange [Hbit Hbefore]].
      split; [lia|]. split; [assumption|]. intros n Hn.
      destruct (Nat.eq_dec n offset) as [->|Hneq]; [exact E|].
      apply Hbefore. lia.
Qed.

Lemma ascii_leading_zeroes_nonzero:
  forall difference,
    difference <> Ascii.zero ->
    exists differing, ascii_leading_zeroes difference = Some differing.
Proof.
  intros difference Hnonzero. unfold ascii_leading_zeroes.
  destruct (ascii_leading_zeroes_from 8 0 difference) as [differing|] eqn:H.
  - eauto.
  - exfalso. apply Hnonzero. apply StringBits.ascii_bit_ext. intros n Hn.
    assert (Hbit : StringBits.ascii_bit difference n = false).
    { apply (proj1 (ascii_leading_zeroes_from_none 8 0 difference) H). lia. }
    destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; cbn in Hbit |- *;
      try exact Hbit; lia.
Qed.

Lemma ascii_first_diff_same:
  forall character, ascii_first_diff character character = None.
Proof.
  intros character. unfold ascii_first_diff. cbn.
  repeat rewrite Bool.eqb_reflx. reflexivity.
Qed.

Lemma xor_first_diff_correct:
  forall left right, xor_first_diff left right = ascii_first_diff left right.
Proof.
  intros left right. unfold xor_first_diff.
  destruct (Ascii.eqb left right) eqn:Heq.
  - apply Ascii.eqb_eq in Heq. subst right.
    now rewrite ascii_first_diff_same.
  - assert (Hneq : left <> right) by (apply Ascii.eqb_neq; exact Heq).
    destruct (ascii_leading_zeroes_nonzero (ascii_xor left right)) as
      [offset Hoffset].
    { intro Hzero. apply Hneq. apply (proj1 (ascii_xor_zero_iff _ _) Hzero). }
    rewrite Hoffset.
    assert (Hoffset_spec := ascii_leading_zeroes_from_some 8 0
      (ascii_xor left right) offset Hoffset).
    destruct Hoffset_spec as [Hrange [Hbit Hbefore]].
    symmetry. apply ascii_first_diff_characterization.
    + rewrite ascii_xor_bit in Hbit by lia.
      destruct (StringBits.ascii_bit left offset),
               (StringBits.ascii_bit right offset); cbn in Hbit;
        try discriminate; discriminate.
    + intros n Hn. pose proof (Hbefore n ltac:(lia)) as Hprior.
      rewrite ascii_xor_bit in Hprior by lia.
      destruct (StringBits.ascii_bit left n), (StringBits.ascii_bit right n);
        cbn in Hprior; try discriminate; reflexivity.
Qed.

(** A safe structural counterpart of the native bytewise scanner.  The
    recursive call consumes one byte from each common prefix; a mismatching
    byte is resolved by [ascii_first_diff], while unequal lengths select the
    continuation-marker tag [0]. *)
Fixpoint bytewise_first_diff (left right : string) : option nat :=
  match left, right with
  | EmptyString, EmptyString => None
  | EmptyString, String _ _ => Some 0
  | String _ _, EmptyString => Some 0
  | String left_ch left_tail, String right_ch right_tail =>
      if Ascii.eqb left_ch right_ch
      then option_map (fun token => 16 + token)
             (bytewise_first_diff left_tail right_tail)
      else option_map S (ascii_first_diff left_ch right_ch)
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
    rewrite Nat.Div0.mod_add.
    rewrite (Nat.mod_small tag 16) by lia. reflexivity. }
  rewrite Hdiv, Hmod.
  symmetry. apply bit_at_logical_position. exact Htag.
Qed.

Lemma packed_bit_at_marker_spec:
  forall s byte,
    packed_bit_at s (packed_position byte 0) = true <->
      byte < String.length s.
Proof.
  intros s byte. unfold packed_bit_at, packed_position.
  assert (Hdiv : (16 * byte + 0) / 16 = byte).
  { replace (16 * byte + 0) with (byte * 16) by lia.
    apply Nat.div_mul. lia. }
  assert (Hmod : (16 * byte + 0) mod 16 = 0).
  { replace (16 * byte + 0) with (byte * 16) by lia.
    apply Nat.Div0.mod_mul. }
  rewrite Hdiv, Hmod.
  destruct (String.get byte s) as [ch|] eqn:Hget.
  - split; intros _.
    + apply Nat.nle_gt. intros Hbound.
      rewrite string_get_past_end in Hget by exact Hbound. discriminate.
    + reflexivity.
  - split.
    + discriminate.
    + intros Hbound. exfalso.
      destruct (string_get_in_bounds s byte Hbound) as [ch Hsome].
      rewrite Hsome in Hget. discriminate.
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

(** The source scanner has a canonical result: an unequal bit following an
    equal prefix is not merely a possible split, but its unique first split.
    This is the form needed to refine a bytewise worker, whose loop invariant
    naturally records the already-compared prefix. *)
Lemma first_diff_characterization:
  forall left right position,
    StringBits.bit_at left position <> StringBits.bit_at right position ->
    (forall n, n < position ->
      StringBits.bit_at left n = StringBits.bit_at right n) ->
    StringBits.first_diff left right = Some position.
Proof.
  intros left right position Hdiff Hbefore.
  destruct (StringBits.first_diff left right) as [differing|] eqn:Hfirst.
  - destruct (StringBits.first_diff_spec left right differing Hfirst)
      as [Hfirst_diff Hfirst_before].
    destruct (Nat.lt_trichotomy position differing) as [Hlt | [Heq | Hgt]].
    + exfalso. apply Hdiff. apply Hfirst_before. exact Hlt.
    + subst differing. reflexivity.
    + exfalso. apply Hfirst_diff. apply Hbefore. exact Hgt.
  - apply StringBits.first_diff_none_iff in Hfirst. subst right.
    exfalso. apply Hdiff. reflexivity.
Qed.

Lemma packed_first_diff_characterization:
  forall left right position,
    packed_bit_at left (encode_position position) <>
      packed_bit_at right (encode_position position) ->
    (forall n, n < position ->
      packed_bit_at left (encode_position n) =
        packed_bit_at right (encode_position n)) ->
    packed_first_diff left right = Some (encode_position position).
Proof.
  intros left right position Hdiff Hbefore.
  apply packed_first_diff_spec.
  apply first_diff_characterization.
  - now rewrite <- !packed_bit_at_encode.
  - intros n Hn. rewrite <- !packed_bit_at_encode. apply Hbefore. exact Hn.
Qed.

(** A native split token is meaningful only when its tag is one of the nine
    source positions in a byte.  On that domain, this is the exact packed
    counterpart of [StringBits.first_diff_spec]: the returned token differs,
    and every earlier *valid* token (represented here by [encode_position])
    agrees. *)
Lemma packed_first_diff_decoded_spec:
  forall left right token,
    packed_first_diff left right = Some token ->
    valid_packed_position token /\
    packed_bit_at left token <> packed_bit_at right token /\
    (forall position, position < decode_position token ->
      packed_bit_at left (encode_position position) =
        packed_bit_at right (encode_position position)).
Proof.
  intros left right token Hfirst.
  assert (Hvalid : valid_packed_position token).
  { unfold packed_first_diff in Hfirst.
    destruct (StringBits.first_diff left right) as [position|] eqn:E;
      cbn in Hfirst; try discriminate.
    injection Hfirst as Htoken. subst token. apply encode_position_valid. }
  assert (Hencoded : packed_first_diff left right =
      Some (encode_position (decode_position token))).
  { now rewrite encode_decode_position. }
  apply packed_first_diff_spec in Hencoded.
  destruct (StringBits.first_diff_spec left right (decode_position token)
    Hencoded) as [Hdiff Hbefore].
  split; [exact Hvalid|]. split.
  - rewrite <- (encode_decode_position token Hvalid).
    now rewrite !packed_bit_at_encode.
  - intros position Hposition.
    rewrite !packed_bit_at_encode. apply Hbefore. exact Hposition.
Qed.

Lemma packed_first_diff_decoded_characterization:
  forall left right token,
    valid_packed_position token ->
    packed_bit_at left token <> packed_bit_at right token ->
    (forall position, position < decode_position token ->
      packed_bit_at left (encode_position position) =
        packed_bit_at right (encode_position position)) ->
    packed_first_diff left right = Some token.
Proof.
  intros left right token Hvalid Hdiff Hbefore.
  rewrite <- (encode_decode_position token Hvalid).
  apply packed_first_diff_characterization.
  - rewrite <- (encode_decode_position token Hvalid) in Hdiff. exact Hdiff.
  - exact Hbefore.
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

Lemma encode_position_next_byte:
  forall position,
    encode_position (9 + position) = 16 + encode_position position.
Proof.
  intros position. unfold encode_position, packed_position.
  assert (Hdiv : (9 + position) / 9 = S (position / 9)).
  { replace (9 + position) with (1 * 9 + position) by lia.
    rewrite Nat.div_add_l by lia. lia. }
  assert (Hmod : (9 + position) mod 9 = position mod 9).
  { replace (9 + position) with (position + 1 * 9) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  rewrite Hdiv, Hmod. lia.
Qed.

Lemma bytewise_first_diff_correct:
  forall left right,
    bytewise_first_diff left right = packed_first_diff left right.
Proof.
  induction left as [|left_ch left_tail IH]; intros right;
    destruct right as [|right_ch right_tail].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn. destruct (Ascii.eqb left_ch right_ch) eqn:Hchar.
    + apply Ascii.eqb_eq in Hchar. subst right_ch.
      rewrite IH.
      destruct (packed_first_diff left_tail right_tail) as [token|] eqn:Htail.
      * assert (Hsource : exists position,
            StringBits.first_diff left_tail right_tail = Some position /\
            token = encode_position position).
        { unfold packed_first_diff in Htail.
          destruct (StringBits.first_diff left_tail right_tail) as [position|]
            eqn:Hfirst; cbn in Htail.
          - injection Htail as Htoken. subst token. eauto.
          - discriminate. }
        destruct Hsource as [position [Hfirst Htoken]]. subst token.
        change (Some (16 + encode_position position) =
          packed_first_diff (String left_ch left_tail)
            (String left_ch right_tail)).
        rewrite <- (encode_position_next_byte position).
        symmetry. apply (proj2 (packed_first_diff_spec _ _ _)).
        apply first_diff_characterization.
        -- rewrite !StringBits.bit_at_cons_tail.
           destruct (StringBits.first_diff_spec _ _ _ Hfirst) as [Hdiff _].
           exact Hdiff.
        -- intros n Hn. destruct (n <? 9) eqn:Hsmall.
           ++ destruct n as [|offset].
              ** reflexivity.
              ** rewrite !StringBits.bit_at_cons_character by
                    (apply Nat.ltb_lt in Hsmall; lia).
                 reflexivity.
           ++ assert (Hdecomp : n = 9 + (n - 9)) by
                 (apply Nat.ltb_ge in Hsmall; lia).
              rewrite Hdecomp, !StringBits.bit_at_cons_tail.
              destruct (StringBits.first_diff_spec _ _ _ Hfirst) as [_ Hbefore].
              apply Hbefore. lia.
      * assert (Hsource : StringBits.first_diff left_tail right_tail = None).
        { unfold packed_first_diff in Htail.
          destruct (StringBits.first_diff left_tail right_tail); cbn in Htail;
            [discriminate|exact Htail]. }
        apply StringBits.first_diff_none_iff in Hsource. subst right_tail.
        unfold packed_first_diff. now rewrite StringBits.first_diff_same.
    + assert (Hneq : left_ch <> right_ch).
      { apply Ascii.eqb_neq. exact Hchar. }
      destruct (ascii_first_diff_unequal_exists left_ch right_ch Hneq)
        as [offset Hoffset].
      change (option_map S (ascii_first_diff left_ch right_ch) =
        packed_first_diff (String left_ch left_tail)
          (String right_ch right_tail)).
      rewrite Hoffset.
      change (Some (S offset) =
        packed_first_diff (String left_ch left_tail)
          (String right_ch right_tail)).
      assert (Hoffset_spec := ascii_first_diff_from_some 8 0
        left_ch right_ch offset Hoffset).
      destruct Hoffset_spec as [Hrange [Hdiff Hbefore]].
      assert (Hencode : encode_position (S offset) = S offset).
      { unfold encode_position, packed_position.
        rewrite Nat.div_small by lia.
        rewrite Nat.mod_small by lia. reflexivity. }
      rewrite <- Hencode.
      symmetry. apply (proj2 (packed_first_diff_spec _ _ _)).
      apply first_diff_characterization.
      * rewrite !StringBits.bit_at_cons_character by lia. exact Hdiff.
      * intros n Hn. destruct n as [|n].
        -- reflexivity.
        -- rewrite !StringBits.bit_at_cons_character by lia.
           apply Hbefore. lia.
Qed.

(** ** The native byte-difference calculation

    [PatriciaExtract.v]'s realizer for [StringBits.first_diff] locates a
    differing byte with a native XOR ([lxor]) and then finds the first
    differing bit with a mask-shift loop (starting at mask [128] and
    shifting right once per step) rather than the safe [ascii_xor]/
    [ascii_leading_zeroes] source model above.  This section states that
    native computation directly, over bounded [N] payloads mirroring OCaml's
    [int], and proves it finds exactly the same split as [ascii_first_diff]
    and, via [bytewise_first_diff_correct], as [StringBits.first_diff]
    itself.  As elsewhere in this file, the residual obligation is only the
    foreign correspondence between these [N] operations and OCaml's own
    [land]/[lxor]/[lsr]/[Char.code] primitives. *)

(** The finite ascii/[N] bit correspondence needed below: [ascii_bit]
    counts from the most significant bit, while [N.testbit] counts from the
    least significant, so position [offset] corresponds to [N] index
    [7 - offset].  Both sides are closed terms once [a]'s eight booleans and
    [offset] are fixed, so this is decided the same brute-force way as
    [ascii_bit_ext] and [ascii_xor_bit] above. *)
Lemma ascii_bit_testbit:
  forall a offset, offset < 8 ->
    StringBits.ascii_bit a offset =
      N.testbit (Ascii.N_of_ascii a) (N.of_nat (7 - offset)).
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] offset Hoffset.
  destruct offset as [|[|[|[|[|[|[|[|offset]]]]]]]]; try lia;
    destruct b0, b1, b2, b3, b4, b5, b6, b7; vm_compute; reflexivity.
Qed.

Lemma N_land_pow2_eqb:
  forall value k, N.eqb (N.land value (N.pow 2 k)) 0 = negb (N.testbit value k).
Proof.
  intros value k. destruct (N.testbit value k) eqn:Htest.
  - apply N.eqb_neq. intro Hzero.
    assert (Hbit : N.testbit (N.land value (N.pow 2 k)) k = false)
      by (rewrite Hzero; apply N.bits_0).
    rewrite N.land_spec, N.pow2_bits_eqb, N.eqb_refl, Htest in Hbit.
    discriminate.
  - apply N.eqb_eq. apply N.bits_inj_0. intros n.
    rewrite N.land_spec, N.pow2_bits_eqb.
    destruct (N.eqb k n) eqn:Ekn.
    + apply N.eqb_eq in Ekn. subst n. rewrite Htest. reflexivity.
    + apply Bool.andb_false_r.
Qed.

(** The mask check at loop position [offset] (mask [2 ^ (7 - offset)],
    matching the realizer's [128 lsr offset]) is nonzero exactly when the
    two byte codes' bits differ at that source position. *)
Definition native_byte_bit (left right : Ascii.ascii) (offset : nat) : bool :=
  negb (N.eqb
    (N.land (N.lxor (Ascii.N_of_ascii left) (Ascii.N_of_ascii right))
       (N.pow 2 (N.of_nat (7 - offset)))) 0).

Lemma native_byte_bit_correct:
  forall left right offset, offset < 8 ->
    native_byte_bit left right offset =
      xorb (StringBits.ascii_bit left offset) (StringBits.ascii_bit right offset).
Proof.
  intros left right offset Hoffset. unfold native_byte_bit.
  rewrite N_land_pow2_eqb, Bool.negb_involutive, N.lxor_spec.
  now rewrite (ascii_bit_testbit left offset Hoffset),
              (ascii_bit_testbit right offset Hoffset).
Qed.

Lemma native_byte_bit_is_ascii_xor_bit:
  forall left right offset, offset < 8 ->
    native_byte_bit left right offset =
      StringBits.ascii_bit (ascii_xor left right) offset.
Proof.
  intros left right offset Hoffset.
  rewrite native_byte_bit_correct by exact Hoffset.
  symmetry. apply ascii_xor_bit. lia.
Qed.

(** [Char.code] exposes the same unsigned byte code used by the native XOR
    model.  This single-byte test is the mathematical meaning of the
    [Char.code ... lsr ... land 1] expression in the [bit_at] realizer; the
    established [N] primitive contract supplies the final link to OCaml's
    shift and mask instructions. *)
Definition native_code_bit (code : N) (offset : nat) : bool :=
  negb (N.eqb
    (N.land code (N.pow 2 (N.of_nat (7 - offset)))) 0).

Lemma native_code_bit_ascii:
  forall ch offset, offset < 8 ->
    native_code_bit (Ascii.N_of_ascii ch) offset =
      StringBits.ascii_bit ch offset.
Proof.
  intros ch offset Hoffset. unfold native_code_bit.
  rewrite N_land_pow2_eqb, Bool.negb_involutive.
  symmetry. apply ascii_bit_testbit. exact Hoffset.
Qed.

(** This follows the control flow of the extracted [bit_at] realizer exactly:
    first test the byte index against native length, then dispatch on the
    packed tag, and only then consume the guarded unsafe byte code. *)
Definition native_packed_bit_at (bytes : list N) (token : nat) : bool :=
  let byte := token / 16 in
  let tag := token mod 16 in
  if byte <? native_byte_length bytes then
    match tag with
    | 0 => true
    | S offset => if offset <? 8 then native_code_bit
        (native_unsafe_byte_code bytes byte) offset else false
    end
  else false.

Theorem native_packed_bit_at_refines:
  forall s token,
    native_packed_bit_at (native_bytes s) token = packed_bit_at s token.
Proof.
  intros s token.
  unfold native_packed_bit_at, packed_bit_at.
  remember (token / 16) as byte.
  remember (token mod 16) as tag.
  rewrite native_bytes_length.
  destruct (byte <? String.length s) eqn:Hbound.
  - apply Nat.ltb_lt in Hbound.
    destruct (string_get_in_bounds s byte Hbound) as [ch Hget].
    rewrite Hget.
    destruct tag as [|offset].
    + reflexivity.
    + destruct (offset <? 8) eqn:Hoffset; [|reflexivity].
      rewrite native_bytes_unsafe_byte_code with (ch := ch) by exact Hget.
      apply native_code_bit_ascii. now apply Nat.ltb_lt.
  - apply Nat.ltb_ge in Hbound.
    rewrite string_get_past_end by exact Hbound. reflexivity.
Qed.

Corollary native_packed_bit_at_refines_representation:
  forall s bytes token,
    native_string_refines s bytes ->
    native_packed_bit_at bytes token = packed_bit_at s token.
Proof.
  intros s bytes token Hrefines. unfold native_string_refines in Hrefines.
  subst bytes. apply native_packed_bit_at_refines.
Qed.

(** The native loop itself: increment [offset] while the mask check misses,
    stop and report [offset] once it hits.  Structurally identical to
    [ascii_leading_zeroes_from], modulo the boolean test used at each step. *)
Fixpoint native_byte_leading_zeroes_from
    (fuel offset : nat) (left right : Ascii.ascii) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if native_byte_bit left right offset
      then Some offset
      else native_byte_leading_zeroes_from fuel' (S offset) left right
  end.

Definition native_byte_leading_zeroes (left right : Ascii.ascii) : option nat :=
  native_byte_leading_zeroes_from 8 0 left right.

Lemma native_byte_leading_zeroes_from_eq:
  forall fuel offset, offset + fuel <= 8 ->
    forall left right,
      native_byte_leading_zeroes_from fuel offset left right =
        ascii_leading_zeroes_from fuel offset (ascii_xor left right).
Proof.
  induction fuel as [|fuel IH]; intros offset Hbound left right; [reflexivity|].
  cbn [native_byte_leading_zeroes_from ascii_leading_zeroes_from].
  rewrite (native_byte_bit_is_ascii_xor_bit left right offset ltac:(lia)).
  destruct (StringBits.ascii_bit (ascii_xor left right) offset).
  - reflexivity.
  - apply IH. lia.
Qed.

Corollary native_byte_leading_zeroes_correct:
  forall left right,
    native_byte_leading_zeroes left right = ascii_leading_zeroes (ascii_xor left right).
Proof.
  intros left right. apply native_byte_leading_zeroes_from_eq. lia.
Qed.

Lemma N_of_ascii_inj:
  forall left right, Ascii.N_of_ascii left = Ascii.N_of_ascii right -> left = right.
Proof.
  intros left right H.
  rewrite <- (Ascii.ascii_N_embedding left), <- (Ascii.ascii_N_embedding right), H.
  reflexivity.
Qed.

Definition native_byte_difference (left right : Ascii.ascii) : N :=
  N.lxor (Ascii.N_of_ascii left) (Ascii.N_of_ascii right).

Lemma native_byte_difference_zero_iff:
  forall left right, native_byte_difference left right = 0%N <-> left = right.
Proof.
  intros left right. unfold native_byte_difference. rewrite N.lxor_eq_0_iff.
  split.
  - apply N_of_ascii_inj.
  - intros ->. reflexivity.
Qed.

(** The full per-byte realizer: an [lxor]-then-zero-check guard, exactly as
    in [PatriciaExtract.v], ahead of the mask loop. *)
Definition native_byte_first_diff (left right : Ascii.ascii) : option nat :=
  if N.eqb (native_byte_difference left right) 0 then None
  else native_byte_leading_zeroes left right.

Theorem native_byte_first_diff_correct:
  forall left right,
    native_byte_first_diff left right = ascii_first_diff left right.
Proof.
  intros left right. unfold native_byte_first_diff.
  destruct (N.eqb (native_byte_difference left right) 0) eqn:E.
  - apply N.eqb_eq in E. apply native_byte_difference_zero_iff in E. subst right.
    symmetry. apply ascii_first_diff_same.
  - assert (Hneq : left <> right).
    { intro Heq. subst right.
      assert (H0 : native_byte_difference left left = 0%N)
        by (apply native_byte_difference_zero_iff; reflexivity).
      rewrite H0, N.eqb_refl in E. discriminate. }
    assert (Heqb : Ascii.eqb left right = false) by (apply Ascii.eqb_neq; exact Hneq).
    rewrite native_byte_leading_zeroes_correct.
    assert (Hcorrect := xor_first_diff_correct left right).
    unfold xor_first_diff in Hcorrect. rewrite Heqb in Hcorrect.
    exact Hcorrect.
Qed.

(** The whole-string realizer, matching [bytewise_first_diff]'s shape with
    the native per-byte guard and loop in place of [Ascii.eqb]/
    [ascii_first_diff]; [native_string_first_diff_refines] closes the chain
    to the packed source model, and so - through [packed_first_diff_spec] -
    to [StringBits.first_diff] itself. *)
Fixpoint native_string_first_diff (left right : string) : option nat :=
  match left, right with
  | EmptyString, EmptyString => None
  | EmptyString, String _ _ => Some 0
  | String _ _, EmptyString => Some 0
  | String left_ch left_tail, String right_ch right_tail =>
      if N.eqb (native_byte_difference left_ch right_ch) 0
      then option_map (fun token => 16 + token)
             (native_string_first_diff left_tail right_tail)
      else option_map S (native_byte_leading_zeroes left_ch right_ch)
  end.

Theorem native_string_first_diff_correct:
  forall left right,
    native_string_first_diff left right = bytewise_first_diff left right.
Proof.
  induction left as [|left_ch left_tail IH]; intros right;
    destruct right as [|right_ch right_tail]; try reflexivity.
  cbn [native_string_first_diff bytewise_first_diff].
  destruct (N.eqb (native_byte_difference left_ch right_ch) 0) eqn:Ediff.
  - assert (Echar : left_ch = right_ch).
    { apply native_byte_difference_zero_iff. now apply N.eqb_eq. }
    subst right_ch. rewrite Ascii.eqb_refl. now rewrite IH.
  - assert (Hneq : left_ch <> right_ch).
    { intro Heq. subst right_ch.
      assert (H0 : native_byte_difference left_ch left_ch = 0%N)
        by (apply native_byte_difference_zero_iff; reflexivity).
      rewrite H0, N.eqb_refl in Ediff. discriminate. }
    assert (Heqb : Ascii.eqb left_ch right_ch = false) by (apply Ascii.eqb_neq; exact Hneq).
    rewrite Heqb, native_byte_leading_zeroes_correct.
    assert (Hcorrect := xor_first_diff_correct left_ch right_ch).
    unfold xor_first_diff in Hcorrect. rewrite Heqb in Hcorrect.
    now rewrite Hcorrect.
Qed.

Corollary native_string_first_diff_refines:
  forall left right,
    native_string_first_diff left right = packed_first_diff left right.
Proof.
  intros left right. rewrite native_string_first_diff_correct.
  apply bytewise_first_diff_correct.
Qed.
