(** Bit operations for a big-endian Patricia tree over [positive] keys.

    A mask is represented by its zero-based bit position.  A prefix is the
    part of a key strictly above that position.  Keeping these two quantities
    as [N] makes the executable model unbounded and avoids an unproved mapping
    to OCaml's finite-width integers. *)

From Stdlib Require Import Bool Lia NArith PArith.

Definition key := positive.

Definition word (k : key) : N := N.pos k.

Definition prefix (k : key) (mask : N) : N :=
  N.shiftr (word k) (N.succ mask).

Definition matches_prefix (k : key) (p mask : N) : bool :=
  N.eqb (prefix k mask) p.

Definition zero_bit (k : key) (mask : N) : bool :=
  negb (N.testbit (word k) mask).

Definition highest_differing_bit (i j : key) : N :=
  N.log2 (N.lxor (word i) (word j)).

Definition mask_above (m1 m2 : N) : bool := N.ltb m2 m1.

Lemma word_injective:
  forall i j, word i = word j -> i = j.
Proof.
  intros i j H. now injection H.
Qed.

Lemma matches_prefix_refl:
  forall k m, matches_prefix k (prefix k m) m = true.
Proof.
  intros. unfold matches_prefix. apply N.eqb_refl.
Qed.

Lemma key_eqb_eq:
  forall i j, Pos.eqb i j = true <-> i = j.
Proof.
  exact Pos.eqb_eq.
Qed.

Lemma key_eqb_neq:
  forall i j, Pos.eqb i j = false <-> i <> j.
Proof.
  exact Pos.eqb_neq.
Qed.

Lemma highest_differing_bit_symmetric:
  forall i j,
    highest_differing_bit i j = highest_differing_bit j i.
Proof.
  intros. unfold highest_differing_bit. now rewrite N.lxor_comm.
Qed.

Lemma mask_above_spec:
  forall m1 m2, mask_above m1 m2 = true <-> (m2 < m1)%N.
Proof.
  intros. unfold mask_above. apply N.ltb_lt.
Qed.

Lemma differing_xor_nonzero:
  forall i j, i <> j -> N.lxor (word i) (word j) <> 0%N.
Proof.
  intros i j Hneq Hzero.
  pose proof (proj1 (N.lxor_eq_0_iff (word i) (word j)) Hzero) as Hij.
  apply word_injective in Hij. contradiction.
Qed.

Lemma highest_prefix_agrees:
  forall i j,
    i <> j ->
    prefix i (highest_differing_bit i j) =
    prefix j (highest_differing_bit i j).
Proof.
  intros i j Hneq.
  unfold prefix, highest_differing_bit.
  apply N.bits_inj. intro n.
  rewrite !N.shiftr_spec by lia.
  apply xorb_eq.
  rewrite <- N.lxor_spec.
  apply N.bits_above_log2. lia.
Qed.

Lemma highest_bit_differs:
  forall i j,
    i <> j ->
    zero_bit i (highest_differing_bit i j) <>
    zero_bit j (highest_differing_bit i j).
Proof.
  intros i j Hneq Heq.
  unfold zero_bit, highest_differing_bit in Heq.
  apply (f_equal negb) in Heq.
  rewrite !negb_involutive in Heq.
  pose proof (N.bit_log2 _ (differing_xor_nonzero i j Hneq)) as Hbit.
  rewrite N.lxor_spec, Heq in Hbit.
  destruct (N.testbit (word j) (N.log2 (N.lxor (word i) (word j))));
    discriminate.
Qed.

Lemma highest_zero_bit_opposite:
  forall i j,
    i <> j ->
    zero_bit j (highest_differing_bit i j) =
    negb (zero_bit i (highest_differing_bit i j)).
Proof.
  intros i j Hneq.
  pose proof (highest_bit_differs i j Hneq).
  destruct (zero_bit i (highest_differing_bit i j));
    destruct (zero_bit j (highest_differing_bit i j));
    simpl in *; congruence.
Qed.

(** Prefix equality is monotone: once two words agree above a bit, they also
    agree above every more significant bit. *)
Lemma prefix_mono:
  forall i j low high,
    (low <= high)%N ->
    prefix i low = prefix j low ->
    prefix i high = prefix j high.
Proof.
  intros i j low high Hle Heq.
  unfold prefix in *.
  assert (E : (N.succ low + (high - low))%N = N.succ high) by lia.
  rewrite <- E, <- !N.shiftr_shiftr.
  now rewrite Heq.
Qed.

Lemma prefix_eq_testbit_above:
  forall i j mask,
    prefix i mask = prefix j mask ->
    forall bit, (mask < bit)%N ->
      N.testbit (word i) bit = N.testbit (word j) bit.
Proof.
  intros i j mask Heq bit Hbit.
  assert (Hshift : (N.succ mask <= bit)%N) by lia.
  pose proof (f_equal (fun n => N.testbit n (bit - N.succ mask)) Heq) as H.
  unfold prefix in H.
  rewrite !N.shiftr_spec' in H.
  replace (bit - N.succ mask + N.succ mask)%N with bit in H by
    (symmetry; apply N.sub_add; exact Hshift).
  exact H.
Qed.

Lemma prefix_mismatch_highest_above:
  forall i j mask,
    prefix i mask <> prefix j mask ->
    (mask < highest_differing_bit i j)%N.
Proof.
  intros i j mask Hprefix.
  assert (Hneq : i <> j).
  { intro E. subst. contradiction. }
  pose proof (highest_prefix_agrees i j Hneq) as Hagree.
  apply N.nle_gt. intro Hle.
  apply Hprefix. eapply prefix_mono; eauto.
Qed.

(** If [j] and [k] belong to a common Patricia prefix which [i] does not
    match, then the first differing bit seen from [i] is independent of which
    member of that prefix is used as representative. *)
Lemma highest_differing_same_prefix:
  forall i j k mask,
    prefix j mask = prefix k mask ->
    prefix i mask <> prefix j mask ->
    highest_differing_bit i j = highest_differing_bit i k.
Proof.
  intros i j k mask Hjk Hij.
  set (d := highest_differing_bit i j).
  assert (Hmd : (mask < d)%N).
  { subst d. now apply prefix_mismatch_highest_above. }
  assert (Hijd : N.testbit (word i) d <> N.testbit (word j) d).
  { assert (Hneq : i <> j) by (intro K; subst; contradiction).
    subst d.
    pose proof (N.bit_log2 _ (differing_xor_nonzero i j Hneq)) as Hbit.
    rewrite N.lxor_spec in Hbit.
    intro E. unfold highest_differing_bit in E.
    rewrite E, xorb_nilpotent in Hbit. discriminate. }
  assert (Hjkd : N.testbit (word j) d = N.testbit (word k) d).
  { eapply prefix_eq_testbit_above; eauto. }
  change (d = N.log2 (N.lxor (word i) (word k))).
  symmetry. apply N.log2_bits_unique.
  - rewrite N.lxor_spec, <- Hjkd.
    destruct (N.testbit (word i) d), (N.testbit (word j) d);
      cbn in *; easy.
  - intros n Hdn. rewrite N.lxor_spec.
    assert (Hijn : N.testbit (word i) n = N.testbit (word j) n).
    { subst d.
      pose proof (N.bits_above_log2 (N.lxor (word i) (word j)) n Hdn) as H.
      rewrite N.lxor_spec in H.
      destruct (N.testbit (word i) n), (N.testbit (word j) n);
        cbn in *; easy. }
    assert (Hjkn : N.testbit (word j) n = N.testbit (word k) n).
    { eapply prefix_eq_testbit_above; eauto. lia. }
    rewrite Hijn, Hjkn. apply xorb_nilpotent.
Qed.

Lemma same_prefix_zero_bit_above:
  forall i j prefix_mask bit,
    prefix i prefix_mask = prefix j prefix_mask ->
    (prefix_mask < bit)%N ->
    zero_bit i bit = zero_bit j bit.
Proof.
  intros. unfold zero_bit.
  now rewrite (prefix_eq_testbit_above _ _ _ H bit H0).
Qed.
