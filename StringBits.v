From Stdlib Require Import Bool Lia PeanoNat Strings.Ascii Strings.String.

(** A prefix-free bit view of byte strings.  Each character is represented by
    a [true] continuation marker followed by its eight bits, most significant
    first.  The end of the string is a [false] marker. *)

Definition ascii_bit (a : ascii) (n : nat) : bool :=
  match a with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7 =>
      match n with
      | 0 => a7 | 1 => a6 | 2 => a5 | 3 => a4
      | 4 => a3 | 5 => a2 | 6 => a1 | _ => a0
      end
  end.

Fixpoint bit_at (s : string) (n : nat) : bool :=
  match s with
  | EmptyString => false
  | String ch rest =>
      match n with
      | 0 => true
      | S offset =>
          if offset <? 8
          then ascii_bit ch offset
          else bit_at rest (offset - 8)
      end
  end.

Definition bit_bound (s : string) : nat := 9 * String.length s + 1.

Fixpoint first_diff_from
    (fuel position : nat) (left right : string) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if Bool.eqb (bit_at left position) (bit_at right position)
      then first_diff_from fuel' (S position) left right
      else Some position
  end.

Definition first_diff (left right : string) : option nat :=
  if String.eqb left right then None
  else first_diff_from (Nat.max (bit_bound left) (bit_bound right)) 0 left right.

Definition agrees_before (left right : string) (split : nat) : bool :=
  match first_diff left right with
  | None => true
  | Some differing => split <=? differing
  end.

Lemma first_diff_same:
  forall s, first_diff s s = None.
Proof.
  intros. unfold first_diff. now rewrite String.eqb_refl.
Qed.

Lemma agrees_before_refl:
  forall s split, agrees_before s s split = true.
Proof.
  intros. unfold agrees_before. now rewrite first_diff_same.
Qed.

(** The bit view is injective.  Notice that this is a theorem about the
    direct string representation; no numerical encoding of whole keys is
    involved. *)

Lemma ascii_bit_ext:
  forall left right,
    (forall n, n < 8 -> ascii_bit left n = ascii_bit right n) ->
    left = right.
Proof.
  intros [l0 l1 l2 l3 l4 l5 l6 l7]
         [r0 r1 r2 r3 r4 r5 r6 r7] H.
  pose proof (H 0 ltac:(lia)) as H0; cbn in H0.
  pose proof (H 1 ltac:(lia)) as H1; cbn in H1.
  pose proof (H 2 ltac:(lia)) as H2; cbn in H2.
  pose proof (H 3 ltac:(lia)) as H3; cbn in H3.
  pose proof (H 4 ltac:(lia)) as H4; cbn in H4.
  pose proof (H 5 ltac:(lia)) as H5; cbn in H5.
  pose proof (H 6 ltac:(lia)) as H6; cbn in H6.
  pose proof (H 7 ltac:(lia)) as H7; cbn in H7.
  congruence.
Qed.

Lemma bit_at_cons_character:
  forall ch rest n,
    n < 8 -> bit_at (String ch rest) (S n) = ascii_bit ch n.
Proof.
  intros ch rest n H. cbn [bit_at].
  apply Nat.ltb_lt in H. now rewrite H.
Qed.

Lemma bit_at_cons_tail:
  forall ch rest n,
    bit_at (String ch rest) (9 + n) = bit_at rest n.
Proof.
  intros. replace (9 + n) with (S (8 + n)) by lia. cbn [bit_at].
  replace (8 + n <? 8) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (8 + n - 8) with n by lia. reflexivity.
Qed.

Lemma bit_at_ext:
  forall left right,
    (forall n, bit_at left n = bit_at right n) -> left = right.
Proof.
  induction left as [|left_ch left_tail IH]; intros right H;
    destruct right as [|right_ch right_tail].
  - reflexivity.
  - specialize (H 0). discriminate.
  - specialize (H 0). discriminate.
  - assert (Hch : left_ch = right_ch).
    { apply ascii_bit_ext. intros n Hn.
      rewrite <- (bit_at_cons_character left_ch left_tail n Hn).
      rewrite <- (bit_at_cons_character right_ch right_tail n Hn).
      apply H. }
    subst right_ch. f_equal. apply IH. intros n.
    rewrite <- (bit_at_cons_tail left_ch left_tail n).
    rewrite <- (bit_at_cons_tail left_ch right_tail n).
    apply H.
Qed.

Lemma bit_at_past_end:
  forall s n, 9 * String.length s <= n -> bit_at s n = false.
Proof.
  induction s as [|ch rest IH]; intros n Hn.
  - reflexivity.
  - destruct n as [|offset].
    + cbn in Hn. lia.
    + cbn [String.length] in Hn. cbn [bit_at].
      destruct (offset <? 8) eqn:E.
      * apply Nat.ltb_lt in E. lia.
      * apply IH. lia.
Qed.

Lemma bit_at_past_bound:
  forall s n, bit_bound s <= n -> bit_at s n = false.
Proof.
  intros. apply bit_at_past_end. unfold bit_bound in H. lia.
Qed.

(** Exact specification of the bounded scanner. *)

Lemma first_diff_from_none:
  forall fuel position left right,
    first_diff_from fuel position left right = None <->
    forall n, position <= n < position + fuel ->
      bit_at left n = bit_at right n.
Proof.
  induction fuel as [|fuel IH]; intros position left right; cbn.
  - split; intros; [lia | reflexivity].
  - destruct (Bool.eqb (bit_at left position) (bit_at right position)) eqn:E.
    + apply Bool.eqb_prop in E. rewrite IH. split.
      * intros H n Hrange. destruct (Nat.eq_dec n position) as [->|Hneq].
        -- exact E.
        -- apply H. lia.
      * intros H n Hrange. apply H. lia.
    + split.
      * discriminate.
      * intros H. exfalso. apply (proj1 (Bool.eqb_false_iff _ _) E).
        apply H. lia.
Qed.

Lemma first_diff_from_some:
  forall fuel position left right differing,
    first_diff_from fuel position left right = Some differing ->
    position <= differing < position + fuel /\
    bit_at left differing <> bit_at right differing /\
    (forall n, position <= n < differing ->
       bit_at left n = bit_at right n).
Proof.
  induction fuel as [|fuel IH]; intros position left right differing H; cbn in H.
  - discriminate.
  - destruct (Bool.eqb (bit_at left position) (bit_at right position)) eqn:E.
    + apply Bool.eqb_prop in E.
      specialize (IH (S position) left right differing H).
      destruct IH as [Hrange [Hdiff Hbefore]].
      split; [lia|]. split; [assumption|]. intros n Hn.
      destruct (Nat.eq_dec n position) as [->|Hneq]; [exact E|].
      apply Hbefore. lia.
    + inversion H; subst differing.
      split; [lia|]. split; [apply (proj1 (Bool.eqb_false_iff _ _) E)|].
      intros; lia.
Qed.

Lemma first_diff_unequal_exists:
  forall left right,
    left <> right -> exists differing, first_diff left right = Some differing.
Proof.
  intros left right Hneq. unfold first_diff.
  assert (Heqb : String.eqb left right = false).
  { apply String.eqb_neq. exact Hneq. }
  rewrite Heqb.
  remember (Nat.max (bit_bound left) (bit_bound right)) as fuel.
  destruct (first_diff_from fuel 0 left right) eqn:E.
  - eauto.
  - exfalso. apply Hneq. apply bit_at_ext. intros n.
    destruct (n <? fuel) eqn:Hnfuel.
    + apply Nat.ltb_lt in Hnfuel.
      apply (proj1 (first_diff_from_none fuel 0 left right) E). lia.
    + pose proof (proj1 (Nat.ltb_ge n fuel) Hnfuel) as Hge.
      assert (Hl : bit_bound left <= n) by
        (rewrite Heqfuel in Hge; eapply Nat.le_trans;
         [apply Nat.le_max_l|exact Hge]).
      assert (Hr : bit_bound right <= n) by
        (rewrite Heqfuel in Hge; eapply Nat.le_trans;
         [apply Nat.le_max_r|exact Hge]).
      now rewrite (bit_at_past_bound left n Hl),
                  (bit_at_past_bound right n Hr).
Qed.

Theorem first_diff_spec:
  forall left right differing,
    first_diff left right = Some differing ->
    bit_at left differing <> bit_at right differing /\
    (forall n, n < differing -> bit_at left n = bit_at right n).
Proof.
  intros left right differing H.
  unfold first_diff in H.
  destruct (String.eqb left right) eqn:E; [discriminate|].
  apply first_diff_from_some in H. destruct H as [_ [Hdiff Hbefore]].
  split; [assumption|]. intros n Hn. apply Hbefore. lia.
Qed.

Corollary first_diff_some_neq:
  forall left right differing,
    first_diff left right = Some differing -> left <> right.
Proof.
  intros left right differing H ->. rewrite first_diff_same in H. discriminate.
Qed.

Theorem first_diff_none_iff:
  forall left right, first_diff left right = None <-> left = right.
Proof.
  intros left right. split.
  - intros H. destruct (String.string_dec left right); [assumption|].
    destruct (first_diff_unequal_exists left right n) as [d Hd]. congruence.
  - intros ->. apply first_diff_same.
Qed.

Theorem agrees_before_spec:
  forall left right split,
    agrees_before left right split = true <->
    forall n, n < split -> bit_at left n = bit_at right n.
Proof.
  intros left right split. unfold agrees_before.
  destruct (first_diff left right) as [d|] eqn:E.
  - rewrite Nat.leb_le. split.
    + intros Hle n Hn. destruct (first_diff_spec _ _ _ E) as [_ Hbefore].
      apply Hbefore. lia.
    + intros Hbefore. destruct (first_diff_spec _ _ _ E) as [Hdiff _].
      apply Nat.nlt_ge. intros Hd. apply Hdiff. apply Hbefore. exact Hd.
  - apply first_diff_none_iff in E. subst. split; intros; [reflexivity|reflexivity].
Qed.
