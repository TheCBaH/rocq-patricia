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

Lemma even_testbit_zero :
  forall word, N.even word = negb (N.testbit word 0).
Proof.
  intros [|word]; [reflexivity|destruct word; reflexivity].
Qed.

Lemma even_odd :
  forall word, N.even word = negb (N.odd word).
Proof.
  intro word. rewrite even_testbit_zero, N.bit0_odd. reflexivity.
Qed.

Lemma bitmap_has_shiftr_even :
  forall bitmap start,
    bitmap_has bitmap start = negb (N.even (N.shiftr bitmap start)).
Proof.
  intros bitmap start. apply eq_true_iff_eq. split; intro H.
  - apply (proj2 (negb_true_iff _)).
    rewrite even_testbit_zero.
    apply (proj2 (negb_false_iff _)).
    rewrite N.shiftr_spec by lia. replace (0 + start)%N with start by lia.
    now apply (proj1 (bitmap_has_spec bitmap start)).
  - apply (proj2 (bitmap_has_spec bitmap start)).
    replace start with (0 + start)%N by lia.
    rewrite <- (N.shiftr_spec bitmap start 0) by lia.
    apply (proj1 (negb_false_iff _)).
    rewrite <- even_testbit_zero.
    apply (proj1 (negb_true_iff _)). exact H.
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

Lemma bitmap_has_land_ones :
  forall bitmap cutoff slot,
    bitmap_has (N.land bitmap (N.ones cutoff)) slot = true <->
    bitmap_has bitmap slot = true /\ (slot < cutoff)%N.
Proof.
  intros bitmap cutoff slot.
  repeat rewrite bitmap_has_spec.
  rewrite N.land_spec, andb_true_iff, N.ones_spec_iff.
  reflexivity.
Qed.

Lemma bitmap_has_land_ones_bool :
  forall bitmap cutoff slot,
    bitmap_has (N.land bitmap (N.ones cutoff)) slot =
    (bitmap_has bitmap slot && N.ltb slot cutoff).
Proof.
  intros bitmap cutoff slot.
  apply eq_true_iff_eq. rewrite bitmap_has_land_ones.
  now rewrite andb_true_iff, N.ltb_lt.
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

Lemma shiftr_succ :
  forall bitmap start,
    N.shiftr bitmap (N.succ start) =
    N.shiftr (N.shiftr bitmap start) 1.
Proof.
  intros bitmap start. rewrite N.shiftr_shiftr.
  replace (start + 1)%N with (N.succ start) by lia. reflexivity.
Qed.

Lemma occupied_slots_from_length_popcount :
  forall fuel bitmap start,
    length (occupied_slots_from fuel bitmap start) =
    popcount_worker fuel (N.shiftr bitmap start).
Proof.
  induction fuel as [|fuel IH]; intros bitmap start; simpl.
  - reflexivity.
  - rewrite bitmap_has_shiftr_even.
    destruct (N.even (N.shiftr bitmap start)) eqn:Heven; simpl;
      rewrite IH, shiftr_succ; reflexivity.
Qed.

Lemma occupied_slots_from_split :
  forall left right bitmap start,
    occupied_slots_from (left + right) bitmap start =
    occupied_slots_from left bitmap start ++
    occupied_slots_from right bitmap (start + N.of_nat left).
Proof.
  induction left as [|left IH]; intros right bitmap start; simpl.
  - now rewrite N.add_0_r.
  - destruct (bitmap_has bitmap start) eqn:Hhas; simpl.
    + rewrite IH.
      assert (Hoffset : (start + N.of_nat (S left))%N =
        (N.succ start + N.of_nat left)%N).
      { now rewrite Nat2N.inj_succ, N.add_succ_r, N.add_succ_l. }
      rewrite <- Hoffset. reflexivity.
    + rewrite IH.
      assert (Hoffset : (start + N.of_nat (S left))%N =
        (N.succ start + N.of_nat left)%N).
      { now rewrite Nat2N.inj_succ, N.add_succ_r, N.add_succ_l. }
      rewrite <- Hoffset. reflexivity.
Qed.

Lemma occupied_slots_from_mask_before_cutoff :
  forall fuel bitmap cutoff start,
    (start + N.of_nat fuel <= cutoff)%N ->
    occupied_slots_from fuel (N.land bitmap (N.ones cutoff)) start =
    occupied_slots_from fuel bitmap start.
Proof.
  induction fuel as [|fuel IH]; intros bitmap cutoff start Hbound; simpl.
  - reflexivity.
  - assert (Hlt : N.ltb start cutoff = true) by
      (apply N.ltb_lt; lia).
    rewrite bitmap_has_land_ones_bool, Hlt. simpl.
    destruct (bitmap_has bitmap start) eqn:Hhas; simpl;
      rewrite (IH bitmap cutoff (N.succ start)) by lia; reflexivity.
Qed.

Lemma occupied_slots_from_mask_after_cutoff :
  forall fuel bitmap cutoff start,
    (cutoff <= start)%N ->
    occupied_slots_from fuel (N.land bitmap (N.ones cutoff)) start = [].
Proof.
  induction fuel as [|fuel IH]; intros bitmap cutoff start Hstart; simpl.
  - reflexivity.
  - destruct (bitmap_has (N.land bitmap (N.ones cutoff)) start) eqn:Hhas.
    + apply (proj1 (bitmap_has_land_ones bitmap cutoff start)) in Hhas.
      lia.
    + apply IH. lia.
Qed.

Lemma occupied_slots_prefix :
  forall cutoff bitmap,
    cutoff <= 32 ->
    occupied_slots bitmap =
    occupied_slots_from cutoff bitmap 0 ++
    occupied_slots_from (32 - cutoff) bitmap (N.of_nat cutoff).
Proof.
  intros cutoff bitmap Hcutoff. unfold occupied_slots.
  replace 32 with (cutoff + (32 - cutoff)) by lia.
  rewrite (occupied_slots_from_split cutoff (32 - cutoff) bitmap 0).
  rewrite N.add_0_l.
  replace (cutoff + (32 - cutoff) - cutoff)%nat with (32 - cutoff) by lia.
  reflexivity.
Qed.

Lemma occupied_slots_length_popcount :
  forall bitmap,
    length (occupied_slots bitmap) = popcount32 bitmap.
Proof.
  intro bitmap. unfold occupied_slots, popcount32.
  rewrite occupied_slots_from_length_popcount. now rewrite N.shiftr_0_r.
Qed.

Lemma rank_occupied_slots_mask :
  forall bitmap slot,
    rank bitmap slot =
    length (occupied_slots (N.land bitmap (N.ones slot))).
Proof.
  intros bitmap slot. unfold rank.
  now rewrite <- occupied_slots_length_popcount.
Qed.

Lemma occupied_slots_from_mask_filter :
  forall fuel bitmap cutoff start,
    occupied_slots_from fuel (N.land bitmap (N.ones cutoff)) start =
    filter (fun slot => N.ltb slot cutoff)
      (occupied_slots_from fuel bitmap start).
Proof.
  induction fuel as [|fuel IH]; intros bitmap cutoff start; simpl.
  - reflexivity.
  - rewrite bitmap_has_land_ones_bool.
    destruct (bitmap_has bitmap start) eqn:Hhas;
      destruct (N.ltb start cutoff) eqn:Hlt;
      simpl; rewrite IH; try rewrite Hlt; reflexivity.
Qed.

Lemma occupied_slots_mask_filter :
  forall bitmap cutoff,
    occupied_slots (N.land bitmap (N.ones cutoff)) =
    filter (fun slot => N.ltb slot cutoff) (occupied_slots bitmap).
Proof.
  intros bitmap cutoff. apply occupied_slots_from_mask_filter.
Qed.

Lemma occupied_slots_prefix_filter :
  forall cutoff bitmap,
    cutoff <= 32 ->
    filter (fun slot => N.ltb slot (N.of_nat cutoff)) (occupied_slots bitmap) =
    occupied_slots_from cutoff bitmap 0.
Proof.
  intros cutoff bitmap Hcutoff.
  rewrite <- (occupied_slots_mask_filter bitmap (N.of_nat cutoff)).
  unfold occupied_slots.
  replace 32 with (cutoff + (32 - cutoff)) by lia.
  rewrite (occupied_slots_from_split cutoff (32 - cutoff)
    (N.land bitmap (N.ones (N.of_nat cutoff))) 0).
  rewrite (@occupied_slots_from_mask_before_cutoff cutoff bitmap
    (N.of_nat cutoff) 0) by lia.
  rewrite N.add_0_l.
  rewrite (@occupied_slots_from_mask_after_cutoff (32 - cutoff) bitmap
    (N.of_nat cutoff) (N.of_nat cutoff)) by lia.
  now rewrite app_nil_r.
Qed.

Lemma rank_occupied_slots_prefix :
  forall bitmap slot,
    rank bitmap slot =
    length (filter (fun occupied => N.ltb occupied slot)
      (occupied_slots bitmap)).
Proof.
  intros bitmap slot. rewrite rank_occupied_slots_mask.
  now rewrite occupied_slots_mask_filter.
Qed.

Lemma rank_occupied_slots_prefix_nat :
  forall bitmap slot,
    slot <= 32 ->
    rank bitmap (N.of_nat slot) =
    length (occupied_slots_from slot bitmap 0).
Proof.
  intros bitmap slot Hslot.
  rewrite rank_occupied_slots_prefix.
  now rewrite occupied_slots_prefix_filter.
Qed.

Lemma occupied_slots_from_at :
  forall slot bitmap,
    bitmap_has bitmap (N.of_nat slot) = true ->
    occupied_slots_from (S slot) bitmap 0 =
    occupied_slots_from slot bitmap 0 ++ [N.of_nat slot].
Proof.
  intros slot bitmap Hhas.
  replace (S slot) with (slot + 1) by lia.
  rewrite (occupied_slots_from_split slot 1 bitmap 0).
  rewrite N.add_0_l. simpl. now rewrite Hhas.
Qed.

Lemma occupied_slots_slot_split :
  forall slot bitmap,
    S slot <= 32 ->
    bitmap_has bitmap (N.of_nat slot) = true ->
    exists after,
      occupied_slots bitmap =
      occupied_slots_from slot bitmap 0 ++ N.of_nat slot :: after.
Proof.
  intros slot bitmap Hslot Hhas.
  exists (occupied_slots_from (32 - S slot) bitmap (N.of_nat (S slot))).
  rewrite (@occupied_slots_prefix (S slot) bitmap) by lia.
  rewrite occupied_slots_from_at by exact Hhas.
  change ((occupied_slots_from slot bitmap 0 ++ [N.of_nat slot]) ++
    occupied_slots_from (32 - S slot) bitmap (N.of_nat (S slot)) =
    occupied_slots_from slot bitmap 0 ++
    ([N.of_nat slot] ++
      occupied_slots_from (32 - S slot) bitmap (N.of_nat (S slot)))).
  symmetry. apply app_assoc.
Qed.

Lemma occupied_slots_rank_split :
  forall slot bitmap,
    S slot <= 32 ->
    bitmap_has bitmap (N.of_nat slot) = true ->
    exists after,
      occupied_slots bitmap =
      occupied_slots_from slot bitmap 0 ++ N.of_nat slot :: after /\
      length (occupied_slots_from slot bitmap 0) =
      rank bitmap (N.of_nat slot).
Proof.
  intros slot bitmap Hslot Hhas.
  destruct (@occupied_slots_slot_split slot bitmap Hslot Hhas) as [after Hsplit].
  exists after. split; [exact Hsplit|].
  symmetry. apply rank_occupied_slots_prefix_nat. lia.
Qed.

Lemma occupied_slots_rank_split_N :
  forall slot bitmap,
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    exists before after,
      occupied_slots bitmap = before ++ slot :: after /\
      length before = rank bitmap slot.
Proof.
  intros slot bitmap Hslot Hhas.
  assert (Hnat : S (N.to_nat slot) <= 32) by
    (unfold branch_width in Hslot; lia).
  rewrite <- (N2Nat.id slot) in Hhas |-.
  destruct (@occupied_slots_rank_split (N.to_nat slot) bitmap Hnat Hhas)
    as [after [Hsplit Hrank]].
  rewrite N2Nat.id in Hsplit, Hrank.
  exists (occupied_slots_from (N.to_nat slot) bitmap 0), after.
  split; assumption.
Qed.

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

Lemma occupied_slots_from_upper :
  forall fuel bitmap start slot,
    In slot (occupied_slots_from fuel bitmap start) ->
    (slot < start + N.of_nat fuel)%N.
Proof.
  induction fuel as [|fuel IH]; intros bitmap start slot Hin; simpl in Hin.
  - contradiction.
  - destruct (bitmap_has bitmap start) eqn:Hstart; simpl in Hin.
    + destruct Hin as [Hslot|Hin].
      * subst slot. simpl. lia.
      * specialize (IH bitmap (N.succ start) slot Hin).
        simpl in IH. lia.
    + specialize (IH bitmap (N.succ start) slot Hin).
      simpl in IH. lia.
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

Lemma bitmap_has_lor_bit_other :
  forall bitmap bit_slot slot,
    slot <> bit_slot ->
    bitmap_has (N.lor bitmap (bitmap_bit bit_slot)) slot =
    bitmap_has bitmap slot.
Proof.
  intros bitmap bit_slot slot Hdifferent.
  destruct (bitmap_has bitmap slot) eqn:Hhas.
  - now apply bitmap_has_lor_left.
  - assert (Hbit : bitmap_has (bitmap_bit bit_slot) slot = false)
      by (now apply bitmap_bit_has_no_other_slot).
    now apply bitmap_has_lor_false.
Qed.

Lemma bitmap_has_ldiff_bit :
  forall bitmap bit_slot,
    bitmap_has (N.ldiff bitmap (bitmap_bit bit_slot)) bit_slot = false.
Proof.
  intros bitmap bit_slot.
  apply (proj2 (bitmap_has_false_spec _ _)).
  unfold bitmap_bit. rewrite N.ldiff_spec, N.shiftl_1_l, N.pow2_bits_true.
  destruct (N.testbit bitmap bit_slot); reflexivity.
Qed.

Lemma bitmap_has_ldiff_bit_other :
  forall bitmap bit_slot slot,
    slot <> bit_slot ->
    bitmap_has (N.ldiff bitmap (bitmap_bit bit_slot)) slot =
    bitmap_has bitmap slot.
Proof.
  intros bitmap bit_slot slot Hdifferent.
  assert (Hbit : N.testbit (bitmap_bit bit_slot) slot = false).
  { apply (proj1 (bitmap_has_false_spec _ _)).
    now apply bitmap_bit_has_no_other_slot. }
  destruct (bitmap_has bitmap slot) eqn:Hhas.
  - apply (proj2 (bitmap_has_spec _ _)).
    apply (proj1 (bitmap_has_spec _ _)) in Hhas.
    now rewrite N.ldiff_spec, Hhas, Hbit.
  - apply (proj2 (bitmap_has_false_spec _ _)).
    apply (proj1 (bitmap_has_false_spec _ _)) in Hhas.
    now rewrite N.ldiff_spec, Hhas, Hbit.
Qed.

Lemma occupied_slots_from_ldiff_bit_away :
  forall fuel bitmap bit_slot start,
    (start + N.of_nat fuel <= bit_slot)%N \/ (bit_slot < start)%N ->
    occupied_slots_from fuel (N.ldiff bitmap (bitmap_bit bit_slot)) start =
    occupied_slots_from fuel bitmap start.
Proof.
  induction fuel as [|fuel IH]; intros bitmap bit_slot start Haway; simpl.
  - reflexivity.
  - assert (Hdifferent : start <> bit_slot) by
      (destruct Haway as [Hbefore|Hafter]; lia).
    rewrite (@bitmap_has_ldiff_bit_other bitmap bit_slot start Hdifferent).
    destruct (bitmap_has bitmap start) eqn:Hhas; simpl;
      rewrite (IH bitmap bit_slot (N.succ start)) by
        (destruct Haway as [Hbefore|Hafter]; [left|right]; lia);
      reflexivity.
Qed.

Lemma occupied_slots_ldiff_bit_present_split :
  forall bitmap slot,
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    exists before after,
      occupied_slots bitmap = before ++ slot :: after /\
      length before = rank bitmap slot /\
      occupied_slots (N.ldiff bitmap (bitmap_bit slot)) = before ++ after.
Proof.
  intros bitmap slot Hslot Hpresent.
  set (slot_nat := N.to_nat slot).
  assert (Hslot_nat : S slot_nat <= 32) by
    (unfold slot_nat; unfold branch_width in Hslot; lia).
  set (before := occupied_slots_from slot_nat bitmap 0).
  set (after := occupied_slots_from (32 - S slot_nat) bitmap
    (N.of_nat (S slot_nat))).
  exists before, after.
  assert (Hbefore :
    occupied_slots_from slot_nat (N.ldiff bitmap (bitmap_bit slot)) 0 = before).
  { unfold before. apply occupied_slots_from_ldiff_bit_away. left.
    unfold slot_nat. rewrite N.add_0_l, N2Nat.id. lia. }
  assert (Hafter :
    occupied_slots_from (32 - S slot_nat)
      (N.ldiff bitmap (bitmap_bit slot)) (N.of_nat (S slot_nat)) = after).
  { unfold after. apply occupied_slots_from_ldiff_bit_away. right.
    unfold slot_nat. rewrite <- (N2Nat.id slot). lia. }
  assert (Hnew_absent :
    bitmap_has (N.ldiff bitmap (bitmap_bit slot)) slot = false)
    by apply bitmap_has_ldiff_bit.
  split.
  - rewrite (@occupied_slots_prefix (S slot_nat) bitmap) by lia.
    rewrite (occupied_slots_from_at slot_nat bitmap).
    + assert (Hslot_id : N.of_nat slot_nat = slot) by
        (unfold slot_nat; apply N2Nat.id).
      unfold before, after. rewrite Hslot_id.
      change ((occupied_slots_from slot_nat bitmap 0 ++ [slot]) ++
        occupied_slots_from (32 - S slot_nat) bitmap (N.of_nat (S slot_nat)) =
        occupied_slots_from slot_nat bitmap 0 ++
        ([slot] ++ occupied_slots_from (32 - S slot_nat) bitmap
          (N.of_nat (S slot_nat)))).
      symmetry. apply app_assoc.
    + unfold slot_nat. rewrite N2Nat.id. exact Hpresent.
  - split.
    + unfold before, slot_nat.
      pose proof (@rank_occupied_slots_prefix_nat bitmap (N.to_nat slot)
        ltac:(lia)) as Hrank.
      now rewrite N2Nat.id in Hrank.
    + rewrite (@occupied_slots_prefix (S slot_nat)
        (N.ldiff bitmap (bitmap_bit slot))) by lia.
      assert (Hnew_prefix :
        occupied_slots_from (S slot_nat)
          (N.ldiff bitmap (bitmap_bit slot)) 0 = before).
      { replace (S slot_nat) with (slot_nat + 1) by lia.
        rewrite (occupied_slots_from_split slot_nat 1
          (N.ldiff bitmap (bitmap_bit slot)) 0).
        rewrite N.add_0_l. simpl.
        assert (Hslot_id : N.of_nat slot_nat = slot) by
          (unfold slot_nat; apply N2Nat.id).
        rewrite Hslot_id, Hnew_absent, app_nil_r, Hbefore. reflexivity. }
      rewrite Hnew_prefix, Hafter.
      reflexivity.
Qed.

Lemma popcount_ldiff_bit_present :
  forall bitmap slot,
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    popcount32 bitmap = S (popcount32 (N.ldiff bitmap (bitmap_bit slot))).
Proof.
  intros bitmap slot Hslot Hpresent.
  destruct (@occupied_slots_ldiff_bit_present_split bitmap slot Hslot Hpresent)
    as [before [after [Hold [Hrank Hnew]]]].
  rewrite <- !occupied_slots_length_popcount.
  rewrite Hold, Hnew.
  repeat rewrite app_length. simpl. lia.
Qed.

Lemma occupied_slots_from_lor_bit_away :
  forall fuel bitmap bit_slot start,
    (start + N.of_nat fuel <= bit_slot)%N \/ (bit_slot < start)%N ->
    occupied_slots_from fuel (N.lor bitmap (bitmap_bit bit_slot)) start =
    occupied_slots_from fuel bitmap start.
Proof.
  induction fuel as [|fuel IH]; intros bitmap bit_slot start Haway; simpl.
  - reflexivity.
  - assert (Hdifferent : start <> bit_slot) by
      (destruct Haway as [Hbefore|Hafter]; lia).
    rewrite (@bitmap_has_lor_bit_other bitmap bit_slot start Hdifferent).
    destruct (bitmap_has bitmap start) eqn:Hhas; simpl;
      rewrite (IH bitmap bit_slot (N.succ start)) by
        (destruct Haway as [Hbefore|Hafter]; [left|right]; lia);
      reflexivity.
Qed.

Lemma occupied_slots_lor_bit_absent_split :
  forall bitmap slot,
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = false ->
    exists before after,
      occupied_slots bitmap = before ++ after /\
      length before = rank bitmap slot /\
      occupied_slots (N.lor bitmap (bitmap_bit slot)) =
        before ++ slot :: after.
Proof.
  intros bitmap slot Hslot Habsent.
  set (slot_nat := N.to_nat slot).
  assert (Hslot_nat : S slot_nat <= 32) by
    (unfold slot_nat; unfold branch_width in Hslot; lia).
  set (before := occupied_slots_from slot_nat bitmap 0).
  set (after := occupied_slots_from (32 - S slot_nat) bitmap
    (N.of_nat (S slot_nat))).
  exists before, after.
  assert (Hold_prefix :
    occupied_slots_from (S slot_nat) bitmap 0 = before).
  { unfold before. replace (S slot_nat) with (slot_nat + 1) by lia.
    rewrite (occupied_slots_from_split slot_nat 1 bitmap 0).
    rewrite N.add_0_l. simpl.
    unfold slot_nat. rewrite N2Nat.id, Habsent, app_nil_r. reflexivity. }
  assert (Hnew_present :
    bitmap_has (N.lor bitmap (bitmap_bit slot)) slot = true).
  { apply bitmap_has_lor_right. apply bitmap_bit_has_slot. }
  assert (Hbefore :
    occupied_slots_from slot_nat (N.lor bitmap (bitmap_bit slot)) 0 = before).
  { unfold before. apply occupied_slots_from_lor_bit_away. left.
    unfold slot_nat. rewrite N.add_0_l, N2Nat.id. lia. }
  assert (Hafter :
    occupied_slots_from (32 - S slot_nat)
      (N.lor bitmap (bitmap_bit slot)) (N.of_nat (S slot_nat)) = after).
  { unfold after. apply occupied_slots_from_lor_bit_away. right.
    unfold slot_nat. rewrite <- (N2Nat.id slot). lia. }
  split.
  - rewrite (@occupied_slots_prefix (S slot_nat) bitmap) by lia.
    rewrite Hold_prefix. exact eq_refl.
  - split.
    + unfold before, slot_nat.
      pose proof (@rank_occupied_slots_prefix_nat bitmap (N.to_nat slot)
        ltac:(lia)) as Hrank.
      now rewrite N2Nat.id in Hrank.
    + rewrite (@occupied_slots_prefix (S slot_nat)
        (N.lor bitmap (bitmap_bit slot))) by lia.
      rewrite (occupied_slots_from_at slot_nat
        (N.lor bitmap (bitmap_bit slot))).
      * assert (Hslot_id : N.of_nat slot_nat = slot) by
          (unfold slot_nat; apply N2Nat.id).
        rewrite Hbefore, Hafter, Hslot_id.
        change ((before ++ [slot]) ++ after = before ++ [slot] ++ after).
        symmetry. apply app_assoc.
      * assert (Hslot_id : N.of_nat slot_nat = slot) by
          (unfold slot_nat; apply N2Nat.id).
        now rewrite Hslot_id.
Qed.

Lemma popcount_lor_bit_absent :
  forall bitmap slot,
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = false ->
    popcount32 (N.lor bitmap (bitmap_bit slot)) = S (popcount32 bitmap).
Proof.
  intros bitmap slot Hslot Habsent.
  destruct (@occupied_slots_lor_bit_absent_split bitmap slot Hslot Habsent)
    as [before [after [Hold [Hrank Hnew]]]].
  rewrite <- !occupied_slots_length_popcount.
  rewrite Hold, Hnew.
  repeat rewrite app_length. simpl. lia.
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

Lemma bitmap_absent_bit_disjoint :
  forall bitmap slot,
    bitmap_has bitmap slot = false ->
    N.land bitmap (bitmap_bit slot) = 0%N.
Proof.
  intros bitmap slot Habsent.
  apply (proj2 (bitmap_land_bit_zero_iff bitmap slot)).
  now apply (proj1 (bitmap_has_false_spec bitmap slot)).
Qed.

Lemma bitmap_lor_bit_bound_absent :
  forall bitmap slot,
    (bitmap < bitmap_limit)%N ->
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = false ->
    (N.lor bitmap (bitmap_bit slot) < bitmap_limit)%N.
Proof.
  intros bitmap slot Hbound Hslot Habsent.
  apply bitmap_lor_bound_disjoint; try assumption.
  - now apply bitmap_bit_bound.
  - now apply bitmap_absent_bit_disjoint.
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

Lemma popcount_lor_bitmap_bits :
  forall left right,
    (left < branch_width)%N ->
    (right < branch_width)%N ->
    left <> right ->
    popcount32 (N.lor (bitmap_bit left) (bitmap_bit right)) = 2.
Proof.
  intros left right Hleft Hright Hdifferent.
  assert (left = 0%N \/ left = 1%N \/ left = 2%N \/ left = 3%N \/ left = 4%N \/ left = 5%N \/ left = 6%N \/ left = 7%N \/ left = 8%N \/ left = 9%N \/ left = 10%N \/ left = 11%N \/ left = 12%N \/ left = 13%N \/ left = 14%N \/ left = 15%N \/ left = 16%N \/ left = 17%N \/ left = 18%N \/ left = 19%N \/ left = 20%N \/ left = 21%N \/ left = 22%N \/ left = 23%N \/ left = 24%N \/ left = 25%N \/ left = 26%N \/ left = 27%N \/ left = 28%N \/ left = 29%N \/ left = 30%N \/ left = 31%N) as Hl by (unfold branch_width in Hleft; lia).
  assert (right = 0%N \/ right = 1%N \/ right = 2%N \/ right = 3%N \/ right = 4%N \/ right = 5%N \/ right = 6%N \/ right = 7%N \/ right = 8%N \/ right = 9%N \/ right = 10%N \/ right = 11%N \/ right = 12%N \/ right = 13%N \/ right = 14%N \/ right = 15%N \/ right = 16%N \/ right = 17%N \/ right = 18%N \/ right = 19%N \/ right = 20%N \/ right = 21%N \/ right = 22%N \/ right = 23%N \/ right = 24%N \/ right = 25%N \/ right = 26%N \/ right = 27%N \/ right = 28%N \/ right = 29%N \/ right = 30%N \/ right = 31%N) as Hr by (unfold branch_width in Hright; lia).
  destruct Hl as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; try contradiction; vm_compute; reflexivity.
Qed.

Lemma occupied_slots_lor_bitmap_bits_lt :
  forall left right,
    (left < branch_width)%N ->
    (right < branch_width)%N ->
    N.ltb left right = true ->
    occupied_slots (N.lor (bitmap_bit left) (bitmap_bit right)) = [left; right].
Proof.
  intros left right Hleft Hright Hlt.
  assert (left = 0%N \/ left = 1%N \/ left = 2%N \/ left = 3%N \/ left = 4%N \/ left = 5%N \/ left = 6%N \/ left = 7%N \/ left = 8%N \/ left = 9%N \/ left = 10%N \/ left = 11%N \/ left = 12%N \/ left = 13%N \/ left = 14%N \/ left = 15%N \/ left = 16%N \/ left = 17%N \/ left = 18%N \/ left = 19%N \/ left = 20%N \/ left = 21%N \/ left = 22%N \/ left = 23%N \/ left = 24%N \/ left = 25%N \/ left = 26%N \/ left = 27%N \/ left = 28%N \/ left = 29%N \/ left = 30%N \/ left = 31%N) as Hl by (unfold branch_width in Hleft; lia).
  assert (right = 0%N \/ right = 1%N \/ right = 2%N \/ right = 3%N \/ right = 4%N \/ right = 5%N \/ right = 6%N \/ right = 7%N \/ right = 8%N \/ right = 9%N \/ right = 10%N \/ right = 11%N \/ right = 12%N \/ right = 13%N \/ right = 14%N \/ right = 15%N \/ right = 16%N \/ right = 17%N \/ right = 18%N \/ right = 19%N \/ right = 20%N \/ right = 21%N \/ right = 22%N \/ right = 23%N \/ right = 24%N \/ right = 25%N \/ right = 26%N \/ right = 27%N \/ right = 28%N \/ right = 29%N \/ right = 30%N \/ right = 31%N) as Hr by (unfold branch_width in Hright; lia).
  destruct Hl as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; try discriminate; vm_compute; reflexivity.
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

Lemma dense_remove_at_append :
  forall A (before : list A) child after,
    dense_remove (length before) (before ++ child :: after) = before ++ after.
Proof.
  intros A before. induction before as [|head before IH]; intros child after.
  - reflexivity.
  - simpl. now rewrite IH.
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

Lemma Forall2_dense_insert :
  forall A B (R : A -> B -> Prop) slots_before slots_after
         children_before children_after (slot : A) (child : B),
    Forall2 R slots_before children_before ->
    R slot child ->
    Forall2 R slots_after children_after ->
    Forall2 R (slots_before ++ slot :: slots_after)
      (dense_insert (length children_before) child
        (children_before ++ children_after)).
Proof.
  intros A B R slots_before slots_after children_before children_after slot child
    Hbefore Hslot Hafter.
  revert children_before Hbefore.
  induction slots_before as [|head slots_before IH];
    intros children_before Hbefore.
  - inversion Hbefore; subst. simpl. constructor; assumption.
  - inversion Hbefore as [|slot' child' slots' children' Hhead Htail]; subst.
    simpl. constructor; [exact Hhead|].
    apply IH; exact Htail.
Qed.
