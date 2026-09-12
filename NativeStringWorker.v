From Stdlib Require Import Bool Lia NArith PeanoNat Strings.Ascii Strings.String Wf_nat.
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
Definition native_eq (left right : nat) : bool := left =? right.
Definition native_min (left right : nat) : nat := Nat.min left right.

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

(** The bounded-prefix worker is kept separate while its refinement proof is
    developed.  Its state invariant and accessibility argument are in [Prop],
    so successful extraction has no fuel argument. *)
Definition native_byte_equal (left right : string) (byte : nat) : bool :=
  match String.get byte left, String.get byte right with
  | Some left_ch, Some right_ch => Ascii.eqb left_ch right_ch
  | None, None => true
  | _, _ => false
  end.

Fixpoint native_ascii_prefix_equal (fuel offset : nat)
    (left right : Ascii.ascii) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
      if Bool.eqb (StringBits.ascii_bit left offset)
          (StringBits.ascii_bit right offset)
      then native_ascii_prefix_equal fuel' (S offset) left right
      else false
  end.

Lemma native_ascii_prefix_equal_refines:
  forall fuel offset left right,
    offset + fuel <= 8 ->
    native_ascii_prefix_equal fuel offset left right =
      NativeRefinement.native_prefix_code_equal fuel offset
        (Ascii.N_of_ascii left) (Ascii.N_of_ascii right).
Proof.
  induction fuel as [|fuel IH]; intros offset left right Hbound;
    cbn [NativeRefinement.native_prefix_code_equal].
  - reflexivity.
  - destruct (Bool.eqb (StringBits.ascii_bit left offset)
        (StringBits.ascii_bit right offset)) eqn:E.
    + rewrite !NativeRefinement.native_code_bit_ascii by lia.
      cbn [native_ascii_prefix_equal]. rewrite E. apply IH. lia.
    + rewrite !NativeRefinement.native_code_bit_ascii by lia.
      cbn [native_ascii_prefix_equal]. now rewrite E.
Qed.

Definition native_terminal_equal
    (left right : string) (byte tag : nat) : bool :=
  if native_eq tag 0 then true else
  match String.get byte left, String.get byte right with
  | Some left_ch, Some right_ch =>
      native_ascii_prefix_equal (native_tag_offset tag) 0 left_ch right_ch
  | None, None => true
  | _, _ => false
  end.

Lemma ascii_eqb_N_eqb:
  forall left right,
    Ascii.eqb left right = N.eqb (Ascii.N_of_ascii left) (Ascii.N_of_ascii right).
Proof.
  intros left right.
  destruct (Ascii.eqb left right) eqn:E.
  - apply Ascii.eqb_eq in E. subst right. symmetry. apply N.eqb_refl.
  - apply Ascii.eqb_neq in E.
    symmetry. apply (proj2 (N.eqb_neq _ _)). intro Hcode. apply E.
    now apply NativeRefinement.N_of_ascii_inj.
Qed.

Lemma native_byte_equal_refines:
  forall left right byte,
    native_byte_equal left right byte =
      NativeRefinement.native_complete_byte_equal
        (NativeRefinement.native_bytes left) (NativeRefinement.native_bytes right) byte.
Proof.
  intros left right byte.
  unfold native_byte_equal.
  rewrite NativeRefinement.native_complete_byte_equal_native_bytes.
  destruct (String.get byte left), (String.get byte right); cbn; try reflexivity.
  apply ascii_eqb_N_eqb.
Qed.

Lemma native_terminal_equal_refines:
  forall left right byte tag,
    tag < 9 ->
    native_terminal_equal left right byte tag =
      NativeRefinement.native_prefix_tag_equal
        (NativeRefinement.native_bytes left) (NativeRefinement.native_bytes right)
        byte tag.
Proof.
  intros left right byte [|count] Htag; [reflexivity|].
  change (native_terminal_equal left right byte (S count) =
    NativeRefinement.native_prefix_tag_equal
      (NativeRefinement.native_bytes left) (NativeRefinement.native_bytes right)
      byte (S count)).
  unfold native_terminal_equal, native_eq.
  rewrite NativeRefinement.native_prefix_tag_equal_native_bytes.
  simpl.
  destruct (String.get byte left), (String.get byte right); cbn; try reflexivity.
  rewrite Nat.sub_0_r.
  exact (native_ascii_prefix_equal_refines count 0 a a0 ltac:(lia)).
Qed.

Lemma native_terminal_mask_expression_refines:
  forall left right tag,
    1 <= tag <= 8 ->
    native_ascii_prefix_equal (tag - 1) 0 left right =
      NativeRefinement.native_terminal_mask_equal left right tag.
Proof.
  intros left right tag Htag.
  rewrite native_ascii_prefix_equal_refines by lia.
  symmetry. now apply NativeRefinement.native_terminal_mask_equal_correct.
Qed.

Lemma native_min_le_left:
  forall left right, native_min left right <= left.
Proof. intros. unfold native_min. apply Nat.le_min_l. Qed.

Lemma native_min_le_right:
  forall left right, native_min left right <= right.
Proof. intros. unfold native_min. apply Nat.le_min_r. Qed.

Lemma bounded_prefix_scan_step:
  forall byte split_byte common,
    byte <= native_min split_byte common ->
    native_eq byte split_byte = false ->
    native_eq byte common = false ->
    S byte <= native_min split_byte common /\
    native_min split_byte common - S byte <
      native_min split_byte common - byte.
Proof.
  intros byte split_byte common Hbound Hsplit Hcommon.
  unfold native_eq in Hsplit, Hcommon.
  apply Nat.eqb_neq in Hsplit, Hcommon.
  assert (Hsplit_le : byte <= split_byte).
  { eapply Nat.le_trans; [exact Hbound|apply native_min_le_left]. }
  assert (Hcommon_le : byte <= common).
  { eapply Nat.le_trans; [exact Hbound|apply native_min_le_right]. }
  assert (Hsplit_lt : byte < split_byte) by lia.
  assert (Hcommon_lt : byte < common) by lia.
  assert (Hmin_lt : byte < native_min split_byte common).
  { unfold native_min.
    destruct (Nat.le_gt_cases split_byte common) as [Horder|Horder].
    - rewrite Nat.min_l by lia. exact Hsplit_lt.
    - rewrite Nat.min_r by lia. exact Hcommon_lt. }
  split; lia.
Qed.

Lemma bounded_prefix_scan_complete_read_safe:
  forall left right split_byte common byte,
    byte <= native_min split_byte common ->
    native_eq byte split_byte = false ->
    native_eq byte common = false ->
    common <= native_length left ->
    common <= native_length right ->
    byte < native_length left /\ byte < native_length right.
Proof.
  intros left right split_byte common byte Hbound Hsplit Hcommon Hleft Hright.
  pose proof (bounded_prefix_scan_step byte split_byte common
    Hbound Hsplit Hcommon) as [Hnext _].
  assert (Hmin_common : native_min split_byte common <= common)
    by apply native_min_le_right.
  assert (Hlt_common : byte < common) by lia.
  split; lia.
Qed.

(** Branch order matches the selected handwritten loop: split terminal,
    common-length sentinel, then complete-byte comparison.  The recursive
    call is possible only while [byte] remains strictly below both sentinels. *)
Fixpoint bounded_prefix_scan_acc
    (left right : string) (split_byte split_tag common byte : nat)
    (Hbyte : byte <= native_min split_byte common)
    (termination : Acc lt (native_min split_byte common - byte))
    {struct termination} : bool :=
  match termination with
  | Acc_intro _ smaller =>
      match native_eq byte split_byte as equal_split
          return native_eq byte split_byte = equal_split -> bool with
      | true => fun _ => native_terminal_equal left right byte split_tag
      | false => fun Hsplit =>
          match native_eq byte common as equal_common
              return native_eq byte common = equal_common -> bool with
          | true => fun _ => native_eq (native_length left) (native_length right)
          | false => fun Hcommon =>
              if native_byte_equal left right byte then
                bounded_prefix_scan_acc left right split_byte split_tag common (S byte)
                  (proj1 (bounded_prefix_scan_step byte split_byte common
                    Hbyte Hsplit Hcommon))
                  (smaller _ (proj2 (bounded_prefix_scan_step byte split_byte common
                    Hbyte Hsplit Hcommon)))
              else false
          end eq_refl
      end eq_refl
  end.

Definition bounded_prefix_scan
    (left right : string) (split_byte split_tag : nat) : bool :=
  let common := native_min (native_length left) (native_length right) in
  bounded_prefix_scan_acc left right split_byte split_tag common 0
    ltac:(unfold native_min; lia) (lt_wf _).

Lemma bounded_prefix_scan_acc_equation:
  forall left right split_byte split_tag common byte Hbyte termination,
    bounded_prefix_scan_acc left right split_byte split_tag common byte Hbyte termination =
      match termination with
      | Acc_intro _ smaller =>
          match native_eq byte split_byte as equal_split
              return native_eq byte split_byte = equal_split -> bool with
          | true => fun _ => native_terminal_equal left right byte split_tag
          | false => fun Hsplit =>
              match native_eq byte common as equal_common
                  return native_eq byte common = equal_common -> bool with
              | true => fun _ => native_eq (native_length left) (native_length right)
              | false => fun Hcommon =>
                  if native_byte_equal left right byte then
                    bounded_prefix_scan_acc left right split_byte split_tag common (S byte)
                      (proj1 (bounded_prefix_scan_step byte split_byte common
                        Hbyte Hsplit Hcommon))
                      (smaller _ (proj2 (bounded_prefix_scan_step byte split_byte common
                        Hbyte Hsplit Hcommon)))
                  else false
              end eq_refl
          end eq_refl
      end.
Proof. intros. destruct termination; reflexivity. Qed.

Lemma bounded_prefix_scan_acc_refines_fuel:
  forall fuel left right split_byte split_tag common byte Hbyte termination,
    native_min split_byte common - byte < fuel -> split_tag < 9 ->
    bounded_prefix_scan_acc left right split_byte split_tag common byte Hbyte termination =
      NativeRefinement.native_bounded_prefix_scan fuel byte split_byte split_tag common
        (NativeRefinement.native_bytes left) (NativeRefinement.native_bytes right).
Proof.
  induction fuel as [|fuel IH]; intros left right split_byte split_tag common byte
    Hbyte [smaller] Hfuel Htag; [lia|].
  cbn [bounded_prefix_scan_acc NativeRefinement.native_bounded_prefix_scan].
  fold (native_eq byte split_byte) (native_eq byte common).
  generalize (eq_refl (native_eq byte split_byte)).
  generalize (native_eq byte split_byte) at 2 3.
  intros split Esplit. destruct split.
  - rewrite Esplit. apply native_terminal_equal_refines. exact Htag.
  - symmetry. rewrite Esplit at 1. symmetry.
    generalize (eq_refl (native_eq byte common)).
    generalize (native_eq byte common) at 2 3.
    intros at_common Ecommon. destruct at_common.
    + rewrite Ecommon. unfold native_eq, native_length.
      now rewrite !NativeRefinement.native_bytes_length.
    + symmetry. rewrite Ecommon at 1. symmetry.
      rewrite <- native_byte_equal_refines.
      destruct (native_byte_equal left right byte); [|reflexivity].
      apply IH; [|exact Htag].
      pose proof (bounded_prefix_scan_step byte split_byte common Hbyte Esplit Ecommon).
      lia.
Qed.

Theorem bounded_prefix_scan_refines:
  forall left right split_byte split_tag,
    split_tag < 9 ->
    bounded_prefix_scan left right split_byte split_tag =
      StringBits.agrees_before_bounded left right
        (NativeRefinement.logical_position split_byte split_tag).
Proof.
  intros left right split_byte split_tag Htag.
  unfold bounded_prefix_scan.
  rewrite (bounded_prefix_scan_acc_refines_fuel (S split_byte)) by
    (try exact Htag; pose proof (native_min_le_left split_byte
      (native_min (native_length left) (native_length right))); lia).
  rewrite <- NativeRefinement.native_bounded_prefix_scan_correct by exact Htag.
  rewrite NativeRefinement.native_common_byte_eq_min, !NativeRefinement.native_bytes_length.
  reflexivity.
Qed.

(** Indexed first-difference candidate.  The tag worker is total only to keep
    its source interface simple; its caller invokes it after a differing-byte
    test, and the later refinement establishes tags 1--8 in that case. *)
Definition native_token_make (byte tag : nat) : nat := 16 * byte + tag.

Fixpoint native_ascii_diff_tag_from (fuel offset : nat)
    (left right : Ascii.ascii) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
      if Bool.eqb (StringBits.ascii_bit left offset)
          (StringBits.ascii_bit right offset)
      then native_ascii_diff_tag_from fuel' (S offset) left right
      else S offset
  end.

Definition native_ascii_diff_tag (left right : Ascii.ascii) : nat :=
  native_ascii_diff_tag_from 8 0 left right.

(** Total source counterpart of the extracted XOR/shifting-mask loop.  The
    byte test is [xor land (128 lsr offset) <> 0]; a caller invokes this only
    after a nonzero byte difference, so the fallback is unreachable there. *)
Fixpoint native_xor_diff_tag_from (fuel offset : nat)
    (left right : Ascii.ascii) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' =>
      if NativeRefinement.native_byte_bit left right offset
      then S offset
      else native_xor_diff_tag_from fuel' (S offset) left right
  end.

Definition native_xor_diff_tag (left right : Ascii.ascii) : nat :=
  native_xor_diff_tag_from 8 0 left right.

Lemma native_ascii_diff_tag_from_range:
  forall fuel offset left right,
    offset + fuel <= 8 ->
    1 <= native_ascii_diff_tag_from fuel offset left right <= 8.
Proof.
  induction fuel as [|fuel IH]; intros offset left right Hbound; cbn.
  - lia.
  - destruct (Bool.eqb (StringBits.ascii_bit left offset)
      (StringBits.ascii_bit right offset)) eqn:E.
    + apply IH. lia.
    + lia.
Qed.

Corollary native_ascii_diff_tag_range:
  forall left right, 1 <= native_ascii_diff_tag left right <= 8.
Proof. intros. unfold native_ascii_diff_tag. apply native_ascii_diff_tag_from_range. lia. Qed.

Lemma native_ascii_diff_tag_from_some:
  forall fuel offset left right differing,
    NativeRefinement.ascii_first_diff_from fuel offset left right = Some differing ->
    native_ascii_diff_tag_from fuel offset left right = S differing.
Proof.
  induction fuel as [|fuel IH]; intros offset left right differing H; cbn in H.
  - discriminate.
  - destruct (Bool.eqb (StringBits.ascii_bit left offset)
      (StringBits.ascii_bit right offset)) eqn:E.
    + cbn. rewrite E. now apply IH.
    + inversion H; subst differing. cbn. now rewrite E.
Qed.

Corollary native_ascii_diff_tag_some:
  forall left right differing,
    NativeRefinement.ascii_first_diff left right = Some differing ->
    native_ascii_diff_tag left right = S differing.
Proof.
  intros. unfold NativeRefinement.ascii_first_diff, native_ascii_diff_tag.
  now apply native_ascii_diff_tag_from_some.
Qed.

Lemma native_xor_diff_tag_from_some:
  forall fuel offset left right differing,
    NativeRefinement.native_byte_leading_zeroes_from fuel offset left right =
      Some differing ->
    native_xor_diff_tag_from fuel offset left right = S differing.
Proof.
  induction fuel as [|fuel IH]; intros offset left right differing H; cbn in H.
  - discriminate.
  - destruct (NativeRefinement.native_byte_bit left right offset) eqn:E.
    + inversion H; subst differing. cbn. now rewrite E.
    + cbn. rewrite E. now apply IH.
Qed.

Lemma native_xor_diff_tag_some:
  forall left right differing,
    NativeRefinement.native_byte_first_diff left right = Some differing ->
    native_xor_diff_tag left right = S differing.
Proof.
  intros left right differing H.
  unfold NativeRefinement.native_byte_first_diff in H.
  destruct (N.eqb (NativeRefinement.native_byte_difference left right) 0)
    eqn:E; cbn in H; try discriminate.
  unfold native_xor_diff_tag.
  now apply native_xor_diff_tag_from_some.
Qed.

Lemma native_xor_diff_tag_range:
  forall left right,
    left <> right -> 1 <= native_xor_diff_tag left right <= 8.
Proof.
  intros left right Hneq.
  assert (Hexists : exists differing,
    NativeRefinement.native_byte_first_diff left right = Some differing).
  { rewrite NativeRefinement.native_byte_first_diff_correct.
    now apply NativeRefinement.ascii_first_diff_unequal_exists. }
  destruct Hexists as [differing Hdiff].
  rewrite (native_xor_diff_tag_some left right differing Hdiff).
  pose proof (NativeRefinement.ascii_first_diff_from_some 8 0 left right
    differing (eq_trans
      (eq_sym (NativeRefinement.native_byte_first_diff_correct left right)) Hdiff))
    as [Hrange _].
  lia.
Qed.

Definition native_byte_diff_tag (left right : string) (byte : nat) : nat :=
  match String.get byte left, String.get byte right with
  | Some left_ch, Some right_ch => native_xor_diff_tag left_ch right_ch
  | _, _ => 1
  end.

(** The executable tag scan shares the byte XOR computed by its caller.
    Only masks and scalar tests are primitives; recursion is extracted from
    this definition and its accessibility evidence is erased. *)
Definition native_difference_bit (difference : N) (offset : nat) : bool :=
  negb (N.eqb (N.land difference (N.pow 2 (N.of_nat (7 - offset)))) 0).

Lemma native_difference_bit_shift_mask:
  forall difference offset, offset <= 7 ->
    native_difference_bit difference offset =
      negb (N.eqb (N.land difference (N.shiftr 128 (N.of_nat offset))) 0).
Proof.
  intros difference [|[|[|[|[|[|[|[|offset]]]]]]]] Hoffset;
    try lia; reflexivity.
Qed.

Lemma difference_tag_step:
  forall offset, offset <= 7 -> native_eq offset 7 = false ->
    S offset <= 7 /\ 7 - S offset < 7 - offset.
Proof. intros offset H E. unfold native_eq in E. apply Nat.eqb_neq in E. lia. Qed.

Fixpoint difference_tag_acc (difference : N) (offset : nat)
    (Hoffset : offset <= 7) (termination : Acc lt (7 - offset))
    {struct termination} : nat :=
  match termination with
  | Acc_intro _ smaller =>
      if native_difference_bit difference offset then S offset
      else match native_eq offset 7 as last
          return native_eq offset 7 = last -> nat with
      | true => fun _ => 1
      | false => fun Hlast => difference_tag_acc difference (S offset)
          (proj1 (difference_tag_step offset Hoffset Hlast))
          (smaller _ (proj2 (difference_tag_step offset Hoffset Hlast)))
      end eq_refl
  end.

Definition difference_tag (difference : N) : nat :=
  difference_tag_acc difference 0 ltac:(lia) (lt_wf _).

Lemma difference_tag_acc_refines:
  forall fuel offset left right Hoffset termination,
    offset + fuel = 8 ->
    difference_tag_acc (NativeRefinement.native_byte_difference left right)
      offset Hoffset termination = native_xor_diff_tag_from fuel offset left right.
Proof.
  induction fuel as [|fuel IH]; intros offset left right Hoffset [smaller] Hfuel;
    [lia|].
  cbn [difference_tag_acc native_xor_diff_tag_from].
  change (native_difference_bit (NativeRefinement.native_byte_difference left right) offset)
    with (NativeRefinement.native_byte_bit left right offset).
  destruct (NativeRefinement.native_byte_bit left right offset); [reflexivity|].
  generalize (eq_refl (native_eq offset 7)).
  generalize (native_eq offset 7) at 2 3.
  intros last Hlast. destruct last.
  - unfold native_eq in Hlast. apply Nat.eqb_eq in Hlast.
    assert (fuel = 0) by lia. subst fuel. reflexivity.
  - apply IH. lia.
Qed.

Corollary difference_tag_refines:
  forall left right,
    difference_tag (NativeRefinement.native_byte_difference left right) =
      native_xor_diff_tag left right.
Proof. intros. apply difference_tag_acc_refines. lia. Qed.

Corollary difference_tag_nonzero_range:
  forall left right,
    NativeRefinement.native_byte_difference left right <> 0%N ->
    1 <= difference_tag (NativeRefinement.native_byte_difference left right) <= 8.
Proof.
  intros left right Hnonzero. rewrite difference_tag_refines.
  apply native_xor_diff_tag_range. intro E. apply Hnonzero.
  apply NativeRefinement.native_byte_difference_zero_iff. exact E.
Qed.

Lemma byte_xor_bound:
  forall left right, (NativeRefinement.native_byte_difference left right < 256)%N.
Proof.
  intros left right.
  pose proof (Ascii.N_ascii_bounded left) as Hl.
  pose proof (Ascii.N_ascii_bounded right) as Hr.
  pose proof (N.log2_le_mono (Ascii.N_of_ascii left) 255 ltac:(lia)) as Hlogl.
  pose proof (N.log2_le_mono (Ascii.N_of_ascii right) 255 ltac:(lia)) as Hlogr.
  change (N.log2 (Ascii.N_of_ascii left) <= 7)%N in Hlogl.
  change (N.log2 (Ascii.N_of_ascii right) <= 7)%N in Hlogr.
  unfold NativeRefinement.native_byte_difference.
  pose proof (N.log2_lxor (Ascii.N_of_ascii left) (Ascii.N_of_ascii right)) as Hxor.
  destruct (N.eq_dec (N.lxor (Ascii.N_of_ascii left) (Ascii.N_of_ascii right)) 0)
    as [E|E]; [rewrite E; reflexivity|].
  change (N.lxor (Ascii.N_of_ascii left) (Ascii.N_of_ascii right) < 2 ^ 8)%N.
  apply (proj2 (N.log2_lt_pow2
    (N.lxor (Ascii.N_of_ascii left) (Ascii.N_of_ascii right)) 8 ltac:(lia))).
  pose proof (N.max_lub _ _ 7 Hlogl Hlogr). lia.
Qed.

Lemma difference_tag_first_set_bit:
  forall left right,
    NativeRefinement.native_byte_difference left right <> 0%N ->
    exists offset, offset < 8 /\
      difference_tag (NativeRefinement.native_byte_difference left right) = S offset /\
      native_difference_bit (NativeRefinement.native_byte_difference left right) offset = true /\
      (forall prior, prior < offset ->
        native_difference_bit (NativeRefinement.native_byte_difference left right) prior = false).
Proof.
  intros left right Hnonzero.
  assert (Hneq : left <> right).
  { intro E. apply Hnonzero. apply NativeRefinement.native_byte_difference_zero_iff. exact E. }
  destruct (NativeRefinement.ascii_leading_zeroes_nonzero
    (NativeRefinement.ascii_xor left right)) as [offset Hscan].
  { intro E. apply Hneq. now apply NativeRefinement.ascii_xor_zero_iff. }
  pose proof (NativeRefinement.ascii_leading_zeroes_from_some 8 0 _ _ Hscan)
    as [Hrange [Hbit Hprior]].
  assert (Hnative : NativeRefinement.native_byte_first_diff left right = Some offset).
  { unfold NativeRefinement.native_byte_first_diff.
    assert (E : N.eqb (NativeRefinement.native_byte_difference left right) 0 = false)
      by (apply N.eqb_neq; exact Hnonzero).
    rewrite E, NativeRefinement.native_byte_leading_zeroes_correct. exact Hscan. }
  exists offset. split; [lia|]. split.
  - rewrite difference_tag_refines. now apply native_xor_diff_tag_some.
  - change (NativeRefinement.native_byte_bit left right offset = true /\
      (forall prior, prior < offset -> NativeRefinement.native_byte_bit left right prior = false)).
    split.
    + rewrite NativeRefinement.native_byte_bit_is_ascii_xor_bit by lia. exact Hbit.
    + intros prior Hp. rewrite NativeRefinement.native_byte_bit_is_ascii_xor_bit by lia.
      apply Hprior. lia.
Qed.

Definition native_byte_xor (left right : string) (byte : nat) : N :=
  NativeRefinement.native_byte_difference
    (native_unsafe_get left byte) (native_unsafe_get right byte).

Definition native_difference_zero (difference : N) : bool := N.eqb difference 0.

Lemma native_byte_xor_correct:
  forall left right byte,
    byte < native_length left -> byte < native_length right ->
    native_difference_zero (native_byte_xor left right byte) =
      native_byte_equal left right byte /\
    difference_tag (native_byte_xor left right byte) =
      native_byte_diff_tag left right byte.
Proof.
  intros left right byte Hleft Hright.
  destruct (NativeRefinement.string_get_in_bounds left byte Hleft) as [lc El].
  destruct (NativeRefinement.string_get_in_bounds right byte Hright) as [rc Er].
  unfold native_byte_xor, native_unsafe_get, native_byte_equal, native_byte_diff_tag.
  rewrite El, Er. split; [|apply difference_tag_refines].
  unfold native_difference_zero.
  destruct (Ascii.eqb lc rc) eqn:E.
  - apply N.eqb_eq. apply NativeRefinement.native_byte_difference_zero_iff.
    now apply Ascii.eqb_eq.
  - apply N.eqb_neq. intro H. apply NativeRefinement.native_byte_difference_zero_iff in H.
    subst rc. rewrite Ascii.eqb_refl in E. discriminate.
Qed.

(** Kept distinct from [native_byte_equal] so first-difference extraction
    emits exactly one byte XOR on every scanned iteration. *)
Definition native_byte_difference_zero (left right : string) (byte : nat) : bool :=
  native_byte_equal left right byte.

Lemma first_diff_scan_step:
  forall byte common,
    byte <= common -> native_eq byte common = false ->
    S byte <= common /\ common - S byte < common - byte.
Proof.
  intros byte common Hbyte Hneq.
  unfold native_eq in Hneq. apply Nat.eqb_neq in Hneq. lia.
Qed.

(** A non-sentinel iteration of the indexed scan reads both strings only
    after the cached common length has established both bounds. *)
Lemma first_diff_scan_complete_read_safe:
  forall left right left_length right_length common byte,
    byte <= common ->
    native_eq byte common = false ->
    common <= left_length -> common <= right_length ->
    left_length = native_length left -> right_length = native_length right ->
    byte < native_length left /\ byte < native_length right.
Proof.
  intros left right left_length right_length common byte Hbyte Hcommon
    Hleft Hright Eleft Eright.
  pose proof (first_diff_scan_step byte common Hbyte Hcommon) as [Hnext _].
  rewrite <- Eleft, <- Eright. lia.
Qed.

(** At a guarded complete-byte iteration, the XOR-zero test is precisely
    character equality.  This is the prior-byte invariant's local step. *)
Lemma native_byte_difference_zero_complete:
  forall left right byte left_ch right_ch,
    String.get byte left = Some left_ch ->
    String.get byte right = Some right_ch ->
    native_byte_difference_zero left right byte = true <-> left_ch = right_ch.
Proof.
  intros left right byte left_ch right_ch Hleft Hright.
  unfold native_byte_difference_zero, native_byte_equal.
  rewrite Hleft, Hright. apply Ascii.eqb_eq.
Qed.

(** A non-extracted structural companion makes the semantic induction over
    completed bytes explicit.  The executable worker below uses erased [Acc]
    instead; this function is proof scaffolding only. *)
Fixpoint first_diff_scan_fuel
    (fuel : nat) (left right : string)
    (left_length right_length common byte : nat) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if native_eq byte common then
        if native_eq left_length right_length then None
        else Some (native_token_make byte 0)
      else if native_byte_difference_zero left right byte then
        first_diff_scan_fuel fuel' left right left_length right_length common (S byte)
      else Some (native_token_make byte (native_byte_diff_tag left right byte))
  end.

Lemma first_diff_scan_fuel_none_prior:
  forall fuel left right left_length right_length common byte,
    common - byte <= fuel ->
    first_diff_scan_fuel fuel left right left_length right_length common byte = None ->
    forall index, byte <= index -> index < common ->
      native_byte_equal left right index = true.
Proof.
  induction fuel as [|fuel IH];
    intros left right left_length right_length common byte Hfuel Hnone
      index Hbyte Hindex; cbn in Hnone.
  - lia.
  - destruct (native_eq byte common) eqn:Ecommon.
    + unfold native_eq in Ecommon. apply Nat.eqb_eq in Ecommon. lia.
    + destruct (native_byte_difference_zero left right byte) eqn:Edifference.
      * destruct (Nat.eq_dec index byte) as [Eindex|Eindex].
        -- subst index. exact Edifference.
        -- apply (IH left right left_length right_length common (S byte)).
           ++ unfold native_eq in Ecommon. apply Nat.eqb_neq in Ecommon. lia.
           ++ exact Hnone.
           ++ lia.
           ++ exact Hindex.
      * discriminate Hnone.
Qed.

Fixpoint first_diff_scan_acc
    (left right : string) (left_length right_length common byte : nat)
    (Hbyte : byte <= common) (termination : Acc lt (common - byte))
    {struct termination} : option nat :=
  match termination with
  | Acc_intro _ smaller =>
      match native_eq byte common as at_common
          return native_eq byte common = at_common -> option nat with
      | true => fun _ =>
          if native_eq left_length right_length then None
          else Some (native_token_make byte 0)
      | false => fun Hcommon =>
          let difference := native_byte_xor left right byte in
          if native_difference_zero difference then
            first_diff_scan_acc left right left_length right_length common (S byte)
              (proj1 (first_diff_scan_step byte common Hbyte Hcommon))
              (smaller _ (proj2 (first_diff_scan_step byte common Hbyte Hcommon)))
          else Some (native_token_make byte (difference_tag difference))
      end eq_refl
  end.

Definition first_diff_indexed (left right : string) : option nat :=
  let left_length := native_length left in
  let right_length := native_length right in
  let common := native_min left_length right_length in
  first_diff_scan_acc left right left_length right_length common 0
    ltac:(unfold native_min; lia) (lt_wf _).

Lemma first_diff_scan_acc_refines_fuel:
  forall fuel left right left_length right_length common byte Hbyte termination,
    common - byte < fuel ->
    common <= native_length left -> common <= native_length right ->
    first_diff_scan_acc left right left_length right_length common byte Hbyte termination =
      first_diff_scan_fuel fuel left right left_length right_length common byte.
Proof.
  induction fuel as [|fuel IH]; intros left right left_length right_length common
    byte Hbyte [smaller] Hfuel Hleft Hright; [lia|].
  cbn [first_diff_scan_acc first_diff_scan_fuel].
  generalize (eq_refl (native_eq byte common)).
  generalize (native_eq byte common) at 2 3.
  intros at_common Ecommon. destruct at_common.
  - now rewrite Ecommon.
  - symmetry. rewrite Ecommon at 1. symmetry.
    pose proof (first_diff_scan_step byte common Hbyte Ecommon) as Hstep.
    destruct (native_byte_xor_correct left right byte ltac:(lia) ltac:(lia)) as [Hzero Htag].
    rewrite Hzero, Htag. unfold native_byte_difference_zero.
    destruct (native_byte_equal left right byte); [|reflexivity].
    apply IH; lia.
Qed.

Lemma first_diff_scan_fuel_cons:
  forall fuel left_ch right_ch left right left_length right_length common byte,
    first_diff_scan_fuel fuel (String left_ch left) (String right_ch right)
      (S left_length) (S right_length) (S common) (S byte) =
    option_map (fun token => 16 + token)
      (first_diff_scan_fuel fuel left right left_length right_length common byte).
Proof.
  induction fuel as [|fuel IH]; intros; [reflexivity|].
  cbn [first_diff_scan_fuel].
  unfold native_eq, native_byte_difference_zero, native_byte_equal, native_byte_diff_tag.
  cbn [String.get Nat.eqb].
  destruct (byte =? common).
  - destruct (left_length =? right_length); [reflexivity|].
    cbn [option_map]. unfold native_token_make. f_equal. lia.
  - destruct (native_byte_equal left right byte) eqn:E;
      unfold native_byte_equal in E; rewrite E.
    + apply IH.
    + cbn [option_map]. unfold native_token_make. f_equal. lia.
Qed.

Lemma first_diff_scan_fuel_refines:
  forall left right fuel,
    Nat.min (String.length left) (String.length right) < fuel ->
    first_diff_scan_fuel fuel left right (String.length left) (String.length right)
      (Nat.min (String.length left) (String.length right)) 0 =
    NativeRefinement.bytewise_first_diff left right.
Proof.
  induction left as [|left_ch left IH]; intros right [|fuel] Hfuel; [lia| |lia|];
    destruct right as [|right_ch right]; try reflexivity.
  cbn [String.length Nat.min] in Hfuel |- *.
  cbn [first_diff_scan_fuel native_eq Nat.eqb native_byte_difference_zero
    native_byte_equal String.get NativeRefinement.bytewise_first_diff].
  destruct (Ascii.eqb left_ch right_ch) eqn:E.
  - rewrite first_diff_scan_fuel_cons. f_equal. apply IH. lia.
  - apply Ascii.eqb_neq in E.
    destruct (NativeRefinement.ascii_first_diff_unequal_exists left_ch right_ch E)
      as [offset Hoffset].
    rewrite Hoffset. cbn [native_byte_diff_tag String.get].
    rewrite (native_xor_diff_tag_some left_ch right_ch offset) by
      (rewrite NativeRefinement.native_byte_first_diff_correct; exact Hoffset).
    reflexivity.
Qed.

Theorem first_diff_indexed_refines:
  forall left right,
    first_diff_indexed left right = NativeRefinement.packed_first_diff left right.
Proof.
  intros left right. unfold first_diff_indexed.
  rewrite (first_diff_scan_acc_refines_fuel
    (S (native_min (native_length left) (native_length right)))) by
      (unfold native_min; pose proof (Nat.le_min_l (native_length left) (native_length right));
       pose proof (Nat.le_min_r (native_length left) (native_length right)); lia).
  rewrite first_diff_scan_fuel_refines by (unfold native_min, native_length; lia).
  rewrite <- NativeRefinement.native_string_first_diff_correct.
  apply NativeRefinement.native_string_first_diff_refines.
Qed.

Corollary first_diff_scan_acc_none_prior:
  forall left right left_length right_length common byte Hbyte termination,
    common <= native_length left -> common <= native_length right ->
    first_diff_scan_acc left right left_length right_length common byte Hbyte termination = None ->
    forall index, byte <= index -> index < common ->
      native_byte_equal left right index = true.
Proof.
  intros left right left_length right_length common byte Hbyte termination Hleft Hright Hnone.
  rewrite (first_diff_scan_acc_refines_fuel (S (common - byte))) in Hnone by lia.
  eapply (first_diff_scan_fuel_none_prior (S (common - byte)) left right
    left_length right_length common byte); [lia|exact Hnone].
Qed.

(** Split production and consumption are compared through the codec.  These
    source facts do not assert that extraction substitutes the representation
    consistently at every map call site. *)
Lemma encoded_position_order:
  forall left right,
    left < right <-> NativeRefinement.encode_position left <
      NativeRefinement.encode_position right.
Proof.
  intros left right.
  pose proof (Nat.div_mod_eq left 9).
  pose proof (Nat.div_mod_eq right 9).
  pose proof (Nat.mod_upper_bound left 9 ltac:(lia)).
  pose proof (Nat.mod_upper_bound right 9 ltac:(lia)).
  unfold NativeRefinement.encode_position, NativeRefinement.packed_position.
  split; lia.
Qed.

Corollary first_diff_indexed_valid:
  forall left right token,
    first_diff_indexed left right = Some token ->
    NativeRefinement.valid_packed_position token.
Proof.
  intros left right token Hdiff. rewrite first_diff_indexed_refines in Hdiff.
  now apply (NativeRefinement.packed_first_diff_valid left right).
Qed.

Corollary first_diff_indexed_spec:
  forall left right position,
    first_diff_indexed left right = Some (NativeRefinement.encode_position position) ->
    StringBits.bit_at left position <> StringBits.bit_at right position /\
    (forall prior, prior < position -> StringBits.bit_at left prior = StringBits.bit_at right prior).
Proof.
  intros left right position Hdiff.
  rewrite first_diff_indexed_refines in Hdiff.
  apply NativeRefinement.packed_first_diff_spec in Hdiff.
  now apply StringBits.first_diff_spec.
Qed.

Definition bounded_prefix_packed (left right : string) (token : nat) : bool :=
  bounded_prefix_scan left right (native_token_byte token) (native_token_tag token).

Theorem bounded_prefix_packed_encode_refines:
  forall left right position,
    bounded_prefix_packed left right (NativeRefinement.encode_position position) =
      StringBits.agrees_before_bounded left right position.
Proof.
  intros left right position.
  unfold bounded_prefix_packed, native_token_byte, native_token_tag.
  rewrite NativeRefinement.encode_position_byte, NativeRefinement.encode_position_tag.
  rewrite bounded_prefix_scan_refines by (apply Nat.mod_upper_bound; lia).
  unfold NativeRefinement.logical_position.
  now rewrite <- Nat.div_mod_eq.
Qed.

(** The source model is deliberately conservative.  Extraction realizes this
    with OCaml physical equality; only a positive result is relied upon. *)
Definition native_string_same (_ _ : string) : bool := false.

Definition first_diff_indexed_with_identity (left right : string) : option nat :=
  if native_string_same left right then None else first_diff_indexed left right.

Lemma first_diff_indexed_identity_shortcut:
  forall same left right,
    NativeRefinement.native_string_same_sound same ->
    same left right = true -> left = right /\
    (if same left right then None else first_diff_indexed left right) = None.
Proof.
  intros same left right Hsound Hsame.
  split.
  - now apply Hsound.
  - now rewrite Hsame.
Qed.

Theorem first_diff_indexed_with_identity_refines:
  forall same left right,
    NativeRefinement.native_string_same_sound same ->
    (if same left right then None else first_diff_indexed left right) =
      NativeRefinement.packed_first_diff left right.
Proof.
  intros same left right Hsame.
  rewrite first_diff_indexed_refines.
  destruct (same left right) eqn:E; [|reflexivity].
  apply Hsame in E. subst right.
  unfold NativeRefinement.packed_first_diff. now rewrite StringBits.first_diff_same.
Qed.
