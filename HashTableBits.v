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

Lemma bitmap_has_empty :
  forall slot, bitmap_has 0 slot = false.
Proof.
  intros slot. unfold bitmap_has.
  now rewrite N.land_0_l.
Qed.

Lemma bitmap_land_bit_zero_iff :
  forall bitmap slot,
    N.land bitmap (bitmap_bit slot) = 0%N <->
    N.testbit bitmap slot = false.
Proof.
  intros bitmap slot. unfold bitmap_bit. rewrite N.shiftl_1_l.
  split.
  - intro Hland.
    assert (Hbit : N.testbit (N.land bitmap (2 ^ slot)) slot = false).
    { now rewrite Hland. }
    rewrite N.land_spec, N.pow2_bits_true, andb_true_r in Hbit.
    exact Hbit.
  - intro Hbit. apply N.bits_inj. intro index.
    rewrite N.land_spec, N.pow2_bits_eqb.
    destruct (N.eqb slot index) eqn:Hequal; simpl.
    + apply N.eqb_eq in Hequal. subst index. now rewrite Hbit.
    + now rewrite andb_false_r.
Qed.

Lemma bitmap_has_spec :
  forall bitmap slot,
    bitmap_has bitmap slot = true <-> N.testbit bitmap slot = true.
Proof.
  intros bitmap slot. unfold bitmap_has.
  destruct (N.testbit bitmap slot) eqn:Hbit.
  - assert (Hnonzero : N.land bitmap (bitmap_bit slot) <> 0%N).
    { intro Hzero. apply (proj1 (bitmap_land_bit_zero_iff bitmap slot)) in Hzero.
      rewrite Hbit in Hzero. discriminate. }
    apply N.eqb_neq in Hnonzero. rewrite Hnonzero. tauto.
  - assert (Hzero : N.land bitmap (bitmap_bit slot) = 0%N).
    { apply (proj2 (bitmap_land_bit_zero_iff bitmap slot)). exact Hbit. }
    rewrite Hzero. tauto.
Qed.

Lemma bitmap_has_false_spec :
  forall bitmap slot,
    bitmap_has bitmap slot = false <-> N.testbit bitmap slot = false.
Proof.
  intros bitmap slot.
  destruct (bitmap_has bitmap slot) eqn:Hhas.
  - destruct (N.testbit bitmap slot) eqn:Hbit.
    + tauto.
    + exfalso. apply (proj1 (bitmap_has_spec bitmap slot)) in Hhas.
      now rewrite Hbit in Hhas.
  - destruct (N.testbit bitmap slot) eqn:Hbit.
    + exfalso. apply (proj2 (bitmap_has_spec bitmap slot)) in Hbit.
      now rewrite Hhas in Hbit.
    + tauto.
Qed.

Lemma bitmap_has_above_limit :
  forall bitmap slot,
    (bitmap < bitmap_limit)%N ->
    (branch_width <= slot)%N ->
    bitmap_has bitmap slot = false.
Proof.
  intros bitmap slot Hbound Hslot.
  apply (proj2 (bitmap_has_false_spec bitmap slot)).
  destruct (N.eq_dec bitmap 0%N) as [Hzero|Hnonzero].
  - subst bitmap. apply N.bits_0.
  - assert (Hpositive : (0 < bitmap)%N) by lia.
    assert (Hpow : (bitmap < 2 ^ 32)%N).
    { change (bitmap < bitmap_limit)%N. exact Hbound. }
    apply (proj1 (N.log2_lt_pow2 bitmap 32 Hpositive)) in Hpow.
    apply N.bits_above_log2. unfold branch_width in Hslot. lia.
Qed.

Lemma bitmap_empty_iff :
  forall bitmap,
    bitmap = 0%N <-> forall slot, bitmap_has bitmap slot = false.
Proof.
  intros bitmap. split.
  - intro Hempty. subst bitmap. apply bitmap_has_empty.
  - intro Habsent. apply N.bits_inj. intro slot.
    rewrite N.bits_0.
    apply (proj1 (bitmap_has_false_spec bitmap slot)). apply Habsent.
Qed.

Lemma occupied_slots_from_empty :
  forall fuel slot, occupied_slots_from fuel 0 slot = [].
Proof.
  induction fuel as [|fuel IH]; intros slot.
  - reflexivity.
  - simpl. apply IH.
Qed.

Lemma occupied_slots_empty : occupied_slots 0 = [].
Proof. apply occupied_slots_from_empty. Qed.

Lemma occupied_slots_from_length_le :
  forall fuel bitmap slot,
    length (occupied_slots_from fuel bitmap slot) <= fuel.
Proof.
  induction fuel as [|fuel IH]; intros bitmap slot.
  - simpl. lia.
  - simpl. destruct (bitmap_has bitmap slot) eqn:Hhas; simpl.
    + specialize (IH bitmap (N.succ slot)). lia.
    + eapply Nat.le_trans; [apply IH|lia].
Qed.

Lemma occupied_slots_length_le :
  forall bitmap, length (occupied_slots bitmap) <= 32.
Proof. intros. apply occupied_slots_from_length_le. Qed.

(** Enumeration is exact over the finite range scanned by the worker.  These
    structural facts are deliberately separate from cardinality/rank: branch
    routing can use them without unfolding the bounded popcount worker. *)
Lemma occupied_slots_from_sound :
  forall fuel bitmap start slot,
    In slot (occupied_slots_from fuel bitmap start) ->
    bitmap_has bitmap slot = true.
Proof.
  induction fuel as [|fuel IH]; intros bitmap start slot Hin; simpl in Hin.
  - contradiction.
  - destruct (bitmap_has bitmap start) eqn:Hstart; simpl in Hin.
    + destruct Hin as [Hslot|Hin].
      * subst slot. exact Hstart.
      * now apply (IH bitmap (N.succ start) slot).
    + now apply (IH bitmap (N.succ start) slot).
Qed.

Lemma occupied_slots_from_complete :
  forall fuel bitmap start slot,
    (start <= slot)%N ->
    (slot < start + N.of_nat fuel)%N ->
    bitmap_has bitmap slot = true ->
    In slot (occupied_slots_from fuel bitmap start).
Proof.
  induction fuel as [|fuel IH]; intros bitmap start slot Hstart Hbound Hhas;
    simpl in Hbound.
  - lia.
  - simpl. destruct (bitmap_has bitmap start) eqn:Hhere.
    + destruct (N.eq_dec slot start) as [Hequal|Hdifferent].
      * subst slot. simpl. now left.
      * simpl. right. apply IH.
        -- lia.
        -- change (slot < N.succ start + N.of_nat fuel)%N. lia.
        -- exact Hhas.
    + simpl. apply IH.
      * destruct (N.eq_dec slot start) as [Hequal|Hdifferent].
        -- subst slot. rewrite Hhas in Hhere. discriminate.
        -- lia.
      * change (slot < N.succ start + N.of_nat fuel)%N. lia.
      * exact Hhas.
Qed.

Lemma occupied_slots_complete :
  forall bitmap slot,
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    In slot (occupied_slots bitmap).
Proof.
  intros bitmap slot Hslot Hhas. unfold occupied_slots.
  apply (occupied_slots_from_complete 32 bitmap).
  - lia.
  - change (slot < branch_width)%N. exact Hslot.
  - exact Hhas.
Qed.

Lemma occupied_slots_from_lower :
  forall fuel bitmap start slot,
    In slot (occupied_slots_from fuel bitmap start) -> (start <= slot)%N.
Proof.
  induction fuel as [|fuel IH]; intros bitmap start slot Hin; simpl in Hin.
  - contradiction.
  - destruct (bitmap_has bitmap start) eqn:Hstart; simpl in Hin.
    + destruct Hin as [Hslot|Hin].
      * subst slot. lia.
      * specialize (IH bitmap (N.succ start) slot Hin). lia.
    + specialize (IH bitmap (N.succ start) slot Hin). lia.
Qed.

Lemma occupied_slots_from_nodup :
  forall fuel bitmap start,
    NoDup (occupied_slots_from fuel bitmap start).
Proof.
  induction fuel as [|fuel IH]; intros bitmap start; simpl.
  - constructor.
  - destruct (bitmap_has bitmap start) eqn:Hstart; simpl.
    + constructor.
      * intro Hin. pose proof (occupied_slots_from_lower fuel bitmap
          (N.succ start) start Hin). lia.
      * apply IH.
    + apply IH.
Qed.

Lemma occupied_slots_nodup : forall bitmap, NoDup (occupied_slots bitmap).
Proof. intros. apply occupied_slots_from_nodup. Qed.

Lemma chunk_bound :
  forall full_hash depth, (chunk full_hash depth < branch_width)%N.
Proof.
  intros. unfold chunk, branch_mask, branch_width.
  pose proof (N.land_le_r (N.shiftr full_hash (N.of_nat (5 * depth))) 31) as H.
  lia.
Qed.

Lemma chunk_zero : forall full_hash, chunk full_hash 0 = N.land full_hash branch_mask.
Proof. intros. reflexivity. Qed.

Lemma chunk_after_hash_bits_zero :
  forall full_hash,
    (full_hash < hash_space)%N ->
    chunk full_hash 6 = 0%N.
Proof.
  intros full_hash Hbound.
  unfold chunk, branch_mask.
  replace (N.of_nat (5 * 6)) with 30%N by reflexivity.
  destruct (N.eq_dec full_hash 0%N) as [Hzero|Hnonzero].
  - subst full_hash. now rewrite N.shiftr_0_l, N.land_0_l.
  - assert (Hpositive : (0 < full_hash)%N) by lia.
    assert (Hpow : (full_hash < 2 ^ 30)%N).
    { change (full_hash < 1073741824)%N. exact Hbound. }
    apply (proj1 (N.log2_lt_pow2 full_hash 30 Hpositive)) in Hpow.
    rewrite N.shiftr_eq_0 by exact Hpow.
    now rewrite N.land_0_l.
Qed.

(** A normalized hash is completely determined by the six chunks used for
    routing.  The least-significant chunk comes first, as it does in the
    executable workers. *)
Lemma chunk_six_reconstruct :
  forall full_hash,
    (full_hash < hash_space)%N ->
    (full_hash = chunk full_hash 0 + 32 * chunk full_hash 1 +
      1024 * chunk full_hash 2 + 32768 * chunk full_hash 3 +
      1048576 * chunk full_hash 4 + 33554432 * chunk full_hash 5)%N.
Proof.
  intros h Hbound.
  unfold chunk, branch_mask.
  change (h = N.land (N.shiftr h 0) (N.ones 5) +
    32 * N.land (N.shiftr h 5) (N.ones 5) +
    1024 * N.land (N.shiftr h 10) (N.ones 5) +
    32768 * N.land (N.shiftr h 15) (N.ones 5) +
    1048576 * N.land (N.shiftr h 20) (N.ones 5) +
    33554432 * N.land (N.shiftr h 25) (N.ones 5))%N.
  rewrite !N.shiftr_div_pow2, !N.land_ones, N.div_1_r.
  change (h = h mod 32 + 32 * ((h / 32) mod 32) +
    1024 * ((h / 1024) mod 32) + 32768 * ((h / 32768) mod 32) +
    1048576 * ((h / 1048576) mod 32) +
    33554432 * ((h / 33554432) mod 32))%N.
  pose proof (N.div_mod h 32 ltac:(lia)) as E0.
  pose proof (N.div_mod (h / 32) 32 ltac:(lia)) as E1.
  pose proof (N.div_mod (h / 1024) 32 ltac:(lia)) as E2.
  pose proof (N.div_mod (h / 32768) 32 ltac:(lia)) as E3.
  pose proof (N.div_mod (h / 1048576) 32 ltac:(lia)) as E4.
  pose proof (N.div_mod (h / 33554432) 32 ltac:(lia)) as E5.
  assert (Q1 : (h / 32 / 32 = h / 1024)%N).
  { change (h / 32 / 32 = h / (32 * 32))%N. apply N.div_div.
    - discriminate. - discriminate. }
  assert (Q2 : (h / 1024 / 32 = h / 32768)%N).
  { change (h / 1024 / 32 = h / (1024 * 32))%N. apply N.div_div.
    - discriminate. - discriminate. }
  assert (Q3 : (h / 32768 / 32 = h / 1048576)%N).
  { change (h / 32768 / 32 = h / (32768 * 32))%N. apply N.div_div.
    - discriminate. - discriminate. }
  assert (Q4 : (h / 1048576 / 32 = h / 33554432)%N).
  { change (h / 1048576 / 32 = h / (1048576 * 32))%N. apply N.div_div.
    - discriminate. - discriminate. }
  assert (Q5 : (h / 33554432 / 32 = 0)%N).
  { rewrite N.div_div.
    - change (h / 1073741824 = 0)%N.
      apply (proj1 (N.le_0_r _)). apply (proj1 (N.lt_succ_r _ 0)).
      apply N.div_lt_upper_bound;
        [discriminate | change (h < 1073741824 * 1)%N; exact Hbound].
    - discriminate. - discriminate. }
  rewrite Q1 in E1. rewrite Q2 in E2. rewrite Q3 in E3.
  rewrite Q4 in E4. rewrite Q5 in E5.
  nia.
Qed.

Lemma chunk_six_ext :
  forall left_hash right_hash,
    (left_hash < hash_space)%N ->
    (right_hash < hash_space)%N ->
    chunk left_hash 0 = chunk right_hash 0 ->
    chunk left_hash 1 = chunk right_hash 1 ->
    chunk left_hash 2 = chunk right_hash 2 ->
    chunk left_hash 3 = chunk right_hash 3 ->
    chunk left_hash 4 = chunk right_hash 4 ->
    chunk left_hash 5 = chunk right_hash 5 ->
    left_hash = right_hash.
Proof.
  intros left_hash right_hash Hleft Hright H0 H1 H2 H3 H4 H5.
  rewrite (chunk_six_reconstruct Hleft).
  rewrite (chunk_six_reconstruct Hright).
  now rewrite H0, H1, H2, H3, H4, H5.
Qed.

(** Distinct normalized hashes diverge in the finite routing domain. *)
Lemma chunk_six_separates :
  forall left_hash right_hash,
    (left_hash < hash_space)%N ->
    (right_hash < hash_space)%N ->
    left_hash <> right_hash ->
    exists depth, depth < branch_levels /\
      chunk left_hash depth <> chunk right_hash depth.
Proof.
  intros left_hash right_hash Hleft Hright Hdifferent.
  destruct (N.eq_dec (chunk left_hash 0) (chunk right_hash 0)) as [H0|H0].
  2: { exists 0. split; [cbv [branch_levels]; lia|exact H0]. }
  destruct (N.eq_dec (chunk left_hash 1) (chunk right_hash 1)) as [H1|H1].
  2: { exists 1. split; [cbv [branch_levels]; lia|exact H1]. }
  destruct (N.eq_dec (chunk left_hash 2) (chunk right_hash 2)) as [H2|H2].
  2: { exists 2. split; [cbv [branch_levels]; lia|exact H2]. }
  destruct (N.eq_dec (chunk left_hash 3) (chunk right_hash 3)) as [H3|H3].
  2: { exists 3. split; [cbv [branch_levels]; lia|exact H3]. }
  destruct (N.eq_dec (chunk left_hash 4) (chunk right_hash 4)) as [H4|H4].
  2: { exists 4. split; [cbv [branch_levels]; lia|exact H4]. }
  destruct (N.eq_dec (chunk left_hash 5) (chunk right_hash 5)) as [H5|H5].
  2: { exists 5. split; [cbv [branch_levels]; lia|exact H5]. }
  exfalso. apply Hdifferent.
  eapply chunk_six_ext; eauto.
Qed.

Lemma bitmap_bit_zero : bitmap_bit 0 = 1%N.
Proof. reflexivity. Qed.

Lemma bitmap_bit_31 : bitmap_bit 31 = 2147483648%N.
Proof. now vm_compute. Qed.

Lemma bitmap_bit_nonzero :
  forall slot, bitmap_bit slot <> 0%N.
Proof.
  intros slot. unfold bitmap_bit.
  rewrite N.shiftl_1_l. now apply N.pow_nonzero.
Qed.

Lemma bitmap_bit_bound :
  forall slot,
    (slot < branch_width)%N ->
    (bitmap_bit slot < bitmap_limit)%N.
Proof.
  intros slot Hslot. unfold bitmap_bit, branch_width, bitmap_limit in *.
  rewrite N.shiftl_1_l.
  change (2 ^ slot < 2 ^ 32)%N.
  apply N.pow_lt_mono_r; lia.
Qed.

Lemma bitmap_bit_has_slot :
  forall slot, bitmap_has (bitmap_bit slot) slot = true.
Proof.
  intros slot. unfold bitmap_bit.
  apply (proj2 (bitmap_has_spec _ _)).
  rewrite N.shiftl_1_l. apply N.pow2_bits_true.
Qed.

Lemma bitmap_bit_has_no_other_slot :
  forall bit_slot slot,
    slot <> bit_slot -> bitmap_has (bitmap_bit bit_slot) slot = false.
Proof.
  intros bit_slot slot Hdifferent. unfold bitmap_bit.
  apply (proj2 (bitmap_has_false_spec _ _)).
  rewrite N.shiftl_1_l, N.pow2_bits_eqb.
  apply N.eqb_neq. now apply not_eq_sym.
Qed.

Lemma bitmap_has_lor_left :
  forall left right slot,
    bitmap_has left slot = true ->
    bitmap_has (N.lor left right) slot = true.
Proof.
  intros left right slot Hleft.
  apply (proj2 (bitmap_has_spec _ _)).
  rewrite N.lor_spec. apply orb_true_intro. left.
  now apply (proj1 (bitmap_has_spec left slot)).
Qed.

Lemma bitmap_has_lor_right :
  forall left right slot,
    bitmap_has right slot = true ->
    bitmap_has (N.lor left right) slot = true.
Proof.
  intros left right slot Hright.
  apply (proj2 (bitmap_has_spec _ _)).
  rewrite N.lor_spec. apply orb_true_intro. right.
  now apply (proj1 (bitmap_has_spec right slot)).
Qed.

Lemma bitmap_has_lor_false :
  forall left right slot,
    bitmap_has left slot = false ->
    bitmap_has right slot = false ->
    bitmap_has (N.lor left right) slot = false.
Proof.
  intros left right slot Hleft Hright.
  apply (proj2 (bitmap_has_false_spec _ _)).
  rewrite N.lor_spec, orb_false_iff. split.
  - now apply (proj1 (bitmap_has_false_spec left slot)).
  - now apply (proj1 (bitmap_has_false_spec right slot)).
Qed.

Lemma bitmap_bits_disjoint :
  forall left_slot right_slot,
    left_slot <> right_slot ->
    N.land (bitmap_bit left_slot) (bitmap_bit right_slot) = 0%N.
Proof.
  intros left_slot right_slot Hdifferent.
  unfold bitmap_bit. rewrite !N.shiftl_1_l.
  apply N.bits_inj. intro index.
  rewrite N.land_spec, !N.pow2_bits_eqb.
  destruct (N.eqb left_slot index) eqn:Hleft;
    destruct (N.eqb right_slot index) eqn:Hright; simpl; auto.
  apply N.eqb_eq in Hleft. apply N.eqb_eq in Hright.
  exfalso. apply Hdifferent. etransitivity; eauto.
Qed.

Lemma bitmap_lor_bound_disjoint :
  forall left right,
    (left < bitmap_limit)%N ->
    (right < bitmap_limit)%N ->
    N.land left right = 0%N ->
    (N.lor left right < bitmap_limit)%N.
Proof.
  intros left right Hleft Hright Hdisjoint.
  rewrite <- (N.lxor_lor left right Hdisjoint).
  rewrite <- (N.add_nocarry_lxor left right Hdisjoint).
  apply N.add_nocarry_lt_pow2 with (n := 32%N); auto.
  all: change (_ < 2 ^ 32)%N; assumption.
Qed.

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

Lemma full_bitmap_has_slot :
  forall slot,
    (slot < branch_width)%N -> bitmap_has full_bitmap slot = true.
Proof.
  intros slot Hslot. apply (proj2 (bitmap_has_spec full_bitmap slot)).
  change (N.testbit (N.ones 32) slot = true).
  now apply N.ones_spec_low.
Qed.

Lemma full_bitmap_has_slot_nat :
  forall slot : nat,
    slot < 32 -> bitmap_has full_bitmap (N.of_nat slot) = true.
Proof.
  intros slot Hslot. apply full_bitmap_has_slot.
  change (N.of_nat slot < N.of_nat 32)%N. lia.
Qed.

Lemma full_bitmap_popcount : popcount32 full_bitmap = 32.
Proof. now vm_compute. Qed.

Lemma popcount_bitmap_bit :
  forall slot,
    (slot < branch_width)%N -> popcount32 (bitmap_bit slot) = 1.
Proof.
  intros slot Hslot.
  assert (slot = 0%N \/ slot = 1%N \/ slot = 2%N \/ slot = 3%N \/ slot = 4%N \/ slot = 5%N \/ slot = 6%N \/ slot = 7%N \/ slot = 8%N \/ slot = 9%N \/ slot = 10%N \/ slot = 11%N \/ slot = 12%N \/ slot = 13%N \/ slot = 14%N \/ slot = 15%N \/ slot = 16%N \/ slot = 17%N \/ slot = 18%N \/ slot = 19%N \/ slot = 20%N \/ slot = 21%N \/ slot = 22%N \/ slot = 23%N \/ slot = 24%N \/ slot = 25%N \/ slot = 26%N \/ slot = 27%N \/ slot = 28%N \/ slot = 29%N \/ slot = 30%N \/ slot = 31%N) as Hcases by (unfold branch_width in Hslot; lia).
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma rank_bitmap_bit_self :
  forall slot,
    (slot < branch_width)%N -> rank (bitmap_bit slot) slot = 0.
Proof.
  intros slot Hslot.
  assert (slot = 0%N \/ slot = 1%N \/ slot = 2%N \/ slot = 3%N \/ slot = 4%N \/ slot = 5%N \/ slot = 6%N \/ slot = 7%N \/ slot = 8%N \/ slot = 9%N \/ slot = 10%N \/ slot = 11%N \/ slot = 12%N \/ slot = 13%N \/ slot = 14%N \/ slot = 15%N \/ slot = 16%N \/ slot = 17%N \/ slot = 18%N \/ slot = 19%N \/ slot = 20%N \/ slot = 21%N \/ slot = 22%N \/ slot = 23%N \/ slot = 24%N \/ slot = 25%N \/ slot = 26%N \/ slot = 27%N \/ slot = 28%N \/ slot = 29%N \/ slot = 30%N \/ slot = 31%N) as Hcases by (unfold branch_width in Hslot; lia).
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma occupied_slots_bitmap_bit :
  forall slot,
    (slot < branch_width)%N -> occupied_slots (bitmap_bit slot) = [slot].
Proof.
  intros slot Hslot.
  assert (slot = 0%N \/ slot = 1%N \/ slot = 2%N \/ slot = 3%N \/ slot = 4%N \/ slot = 5%N \/ slot = 6%N \/ slot = 7%N \/ slot = 8%N \/ slot = 9%N \/ slot = 10%N \/ slot = 11%N \/ slot = 12%N \/ slot = 13%N \/ slot = 14%N \/ slot = 15%N \/ slot = 16%N \/ slot = 17%N \/ slot = 18%N \/ slot = 19%N \/ slot = 20%N \/ slot = 21%N \/ slot = 22%N \/ slot = 23%N \/ slot = 24%N \/ slot = 25%N \/ slot = 26%N \/ slot = 27%N \/ slot = 28%N \/ slot = 29%N \/ slot = 30%N \/ slot = 31%N) as Hcases by (unfold branch_width in Hslot; lia).
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma full_bitmap_rank_slot_31 : rank full_bitmap 31 = 31.
Proof. now vm_compute. Qed.

Lemma full_bitmap_rank_nat :
  forall slot : nat,
    slot < 32 -> rank full_bitmap (N.of_nat slot) = slot.
Proof.
  intros slot Hslot.
  assert (slot = 0 \/ slot = 1 \/ slot = 2 \/ slot = 3 \/ slot = 4 \/ slot = 5 \/ slot = 6 \/ slot = 7 \/ slot = 8 \/ slot = 9 \/ slot = 10 \/ slot = 11 \/ slot = 12 \/ slot = 13 \/ slot = 14 \/ slot = 15 \/ slot = 16 \/ slot = 17 \/ slot = 18 \/ slot = 19 \/ slot = 20 \/ slot = 21 \/ slot = 22 \/ slot = 23 \/ slot = 24 \/ slot = 25 \/ slot = 26 \/ slot = 27 \/ slot = 28 \/ slot = 29 \/ slot = 30 \/ slot = 31) as Hcases by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; vm_compute; reflexivity.
Qed.

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

Lemma dense_remove_length_hit :
  forall A index (children : list A),
    index < length children ->
    length (dense_remove index children) = Nat.pred (length children).
Proof.
  intros A index. induction index as [|index IH]; intros children Hbound.
  - destruct children as [|head tail]; simpl in Hbound; try lia. reflexivity.
  - destruct children as [|head tail]; simpl in Hbound; try lia.
    simpl. rewrite IH by lia.
    apply Nat.succ_pred_pos. lia.
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
  - destruct children as [|head tail]; reflexivity.
  - destruct children as [|head tail]; simpl in Hbound.
    + lia.
    + simpl. unfold dense_get in IH. apply IH. lia.
Qed.

Lemma dense_get_insert_before :
  forall A index before (child : A) children,
    before < index ->
    index <= length children ->
    dense_get before (dense_insert index child children) = dense_get before children.
Proof.
  intros A index. induction index as [|index IH];
    intros before child children Hbefore Hbound.
  - lia.
  - destruct before as [|before].
    + destruct children as [|head tail]; simpl in Hbound; try lia. reflexivity.
    + destruct children as [|head tail]; simpl in Hbound; try lia.
      simpl. apply IH; lia.
Qed.

Lemma dense_get_insert_after :
  forall A index after (child : A) children,
    index <= after ->
    index <= length children ->
    dense_get (S after) (dense_insert index child children) = dense_get after children.
Proof.
  intros A index. induction index as [|index IH];
    intros after child children Hafter Hbound.
  - destruct children as [|head tail].
    + destruct after; reflexivity.
    + reflexivity.
  - destruct after as [|after]; simpl in Hafter; try lia.
    destruct children as [|head tail]; simpl in Hbound; try lia.
    simpl. apply IH; lia.
Qed.

Lemma dense_insert_in :
  forall A index (child : A) children item,
    In item (dense_insert index child children) <-> item = child \/ In item children.
Proof.
  intros A index. induction index as [|index IH]; intros child children item.
  - simpl. intuition subst; auto.
  - destruct children as [|head tail].
    + simpl. intuition subst; auto.
    + simpl. rewrite IH. intuition subst; auto.
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

Lemma dense_get_replace_other :
  forall A index other (child : A) children,
    other <> index ->
    dense_get other (dense_replace index child children) = dense_get other children.
Proof.
  intros A index. induction index as [|index IH];
    intros other child children Hother.
  - destruct other as [|other]; [contradiction|].
    destruct children; reflexivity.
  - destruct other as [|other].
    + destruct children; reflexivity.
    + destruct children as [|head tail].
      * reflexivity.
      * simpl. apply IH. intro Heq. apply Hother. now f_equal.
Qed.

Lemma dense_replace_in :
  forall A index (child : A) children item,
    index < length children ->
    In item (dense_replace index child children) ->
    item = child \/ In item children.
Proof.
  intros A index. induction index as [|index IH];
    intros child children item Hbound Hin.
  - destruct children as [|head tail]; simpl in Hbound; try lia.
    simpl in Hin. destruct Hin as [Hin|Hin].
    + now left; symmetry.
    + now right; right.
  - destruct children as [|head tail]; simpl in Hbound; try lia.
    simpl in Hin. destruct Hin as [Hin|Hin].
    + now right; left.
    + specialize (IH child tail item ltac:(lia) Hin).
      destruct IH as [IH|IH].
      * now left.
      * now right; right.
Qed.

Lemma dense_get_remove_before :
  forall A index before (children : list A),
    before < index ->
    dense_get before (dense_remove index children) = dense_get before children.
Proof.
  intros A index. induction index as [|index IH]; intros before children Hbefore.
  - lia.
  - destruct before as [|before].
    + destruct children; reflexivity.
    + destruct children as [|head tail]; simpl; auto.
      apply IH. lia.
Qed.

Lemma dense_get_remove_after :
  forall A index after (children : list A),
    index <= after ->
    dense_get after (dense_remove index children) = dense_get (S after) children.
Proof.
  intros A index. induction index as [|index IH]; intros after children Hafter.
  - destruct children as [|head tail].
    + destruct after; reflexivity.
    + reflexivity.
  - destruct after as [|after]; simpl in Hafter; try lia.
    destruct children as [|head tail]; simpl; auto.
    apply IH. lia.
Qed.

Lemma dense_remove_in :
  forall A index (children : list A) item,
    In item (dense_remove index children) -> In item children.
Proof.
  intros A index. induction index as [|index IH]; intros children item Hin.
  - destruct children as [|head tail]; simpl in *; auto.
  - destruct children as [|head tail]; simpl in *; auto.
    destruct Hin as [Hin|Hin]; [now left|].
    now right; apply IH.
Qed.

Lemma Forall2_dense_replace :
  forall A B (R : A -> B -> Prop) index (child : B) slots children,
    Forall2 R slots children ->
    index < length children ->
    (forall slot old_child,
        nth_error slots index = Some slot ->
        nth_error children index = Some old_child ->
        R slot child) ->
    Forall2 R slots (dense_replace index child children).
Proof.
  intros A B R index.
  induction index as [|index IH]; intros child slots children Hpaired Hbound Hnew.
  - destruct children as [|old_child tail]; simpl in Hbound; [lia|].
    inversion Hpaired as [|slot child' slots' children' Hhead Htail]; subst.
    simpl. constructor.
    + apply (Hnew slot old_child); reflexivity.
    + exact Htail.
  - destruct children as [|old_child tail]; simpl in Hbound; [lia|].
    inversion Hpaired as [|slot child' slots' children' Hhead Htail]; subst.
    simpl. constructor; [exact Hhead|].
    apply IH; [exact Htail|lia|].
    intros slot' old_child' Hslot Hchild.
    apply (Hnew slot' old_child'); simpl; exact Hslot || exact Hchild.
Qed.
