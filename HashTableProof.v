(** Initial correctness lemmas for the executable HAMT source model.

    These base cases deliberately live outside [HashTable.v].  The recursive
    routing/invariant development can therefore build on stable operational
    equations without conflating specification and implementation. *)

From Stdlib Require Import Arith Bool Lia List NArith SetoidList.
Import ListNotations.

Require Import HashTableSpec HashTable HashTableBits HashTableBucket.

Set Implicit Arguments.

(** The invariant is parameterized by the key equivalence and normalized
    source hash.  Prefixes are stored least-significant chunk first, matching
    [chunk] and the runtime routing order. *)
Section WellFormed.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

  Definition binding_equiv (left right : K * A) : Prop :=
    E (fst left) (fst right).

  (** A prefix records chunks from the root.  The current routing depth is
      tracked separately by [wf]; scanning a prefix always begins at chunk 0. *)
  Fixpoint prefix_matches_from (full_hash : N) (start : nat)
      (prefix : list N) : Prop :=
    match prefix with
    | [] => True
    | slot :: rest =>
        chunk full_hash start = slot /\
        prefix_matches_from full_hash (S start) rest
    end.

  Definition prefix_matches (full_hash : N) (_depth : nat)
      (prefix : list N) : Prop :=
    prefix_matches_from full_hash 0 prefix.

Lemma prefix_matches_from_append_slot :
    forall full_hash start prefix,
      prefix_matches_from full_hash start prefix ->
      prefix_matches_from full_hash start
        (prefix ++ [chunk full_hash (start + length prefix)]).
  Proof.
    intros full_hash start prefix Hprefix. revert start Hprefix.
    induction prefix as [|head tail IH]; intros start Hprefix.
    - simpl. replace (start + 0) with start by lia.
      split; [reflexivity|exact I].
    - simpl in Hprefix. destruct Hprefix as [Hhead Htail]. simpl.
      split; [exact Hhead|].
      replace (start + S (length tail)) with (S start + length tail) by lia.
      apply IH. exact Htail.
  Qed.

Lemma prefix_matches_append_slot :
    forall full_hash depth prefix,
      length prefix = depth ->
      prefix_matches full_hash depth prefix ->
      prefix_matches full_hash (S depth) (prefix ++ [chunk full_hash depth]).
  Proof.
    intros full_hash depth prefix Hlength Hprefix.
    unfold prefix_matches in *. rewrite <- Hlength.
    apply prefix_matches_from_append_slot. exact Hprefix.
  Qed.

Lemma prefix_matches_from_agree :
    forall start prefix left_hash right_hash index,
      prefix_matches_from left_hash start prefix ->
      prefix_matches_from right_hash start prefix ->
      index < length prefix ->
      chunk left_hash (start + index) = chunk right_hash (start + index).
  Proof.
    intros start prefix. revert start.
    induction prefix as [|slot prefix IH]; intros start left_hash right_hash index
      Hleft Hright Hindex.
    - simpl in Hindex. lia.
    - simpl in Hleft, Hright. destruct Hleft as [Hleft Hleft_tail].
      destruct Hright as [Hright Hright_tail]. destruct index as [|index].
      + replace (start + 0) with start by lia. now rewrite Hleft, Hright.
      + cbn in Hindex. replace (start + S index) with (S start + index) by lia.
        eapply IH; [exact Hleft_tail|exact Hright_tail|lia].
  Qed.

Lemma prefix_matches_agree :
    forall depth prefix left_hash right_hash prior,
      length prefix = depth ->
      prefix_matches left_hash depth prefix ->
      prefix_matches right_hash depth prefix ->
      prior < depth ->
      chunk left_hash prior = chunk right_hash prior.
  Proof.
    intros depth prefix left_hash right_hash prior Hlength Hleft Hright Hprior.
    unfold prefix_matches in Hleft, Hright.
    replace prior with (0 + prior) by lia.
    apply prefix_matches_from_agree with (prefix := prefix); try assumption.
    now rewrite Hlength.
  Qed.

Lemma prefix_matches_from_app_prefix :
    forall full_hash start prefix suffix,
      prefix_matches_from full_hash start (prefix ++ suffix) ->
      prefix_matches_from full_hash start prefix.
  Proof.
    intros full_hash start prefix. revert start.
    induction prefix as [|slot prefix IH]; intros start suffix Hmatches.
    - exact I.
    - simpl in Hmatches. destruct Hmatches as [Hslot Htail]. simpl.
      split; [exact Hslot|].
      apply IH with (suffix := suffix). exact Htail.
  Qed.

Lemma prefix_matches_from_app_last :
    forall full_hash start prefix slot,
      prefix_matches_from full_hash start (prefix ++ [slot]) ->
      chunk full_hash (start + length prefix) = slot.
  Proof.
    intros full_hash start prefix. revert start.
    induction prefix as [|head prefix IH]; intros start slot Hmatches.
    - simpl in Hmatches. destruct Hmatches as [Hslot _].
      rewrite Nat.add_0_r. exact Hslot.
    - simpl in Hmatches. destruct Hmatches as [_ Htail].
      assert (Hindex : start + length (head :: prefix) =
        S start + length prefix).
      { simpl. lia. }
      rewrite Hindex.
      apply IH. exact Htail.
  Qed.

Lemma prefix_matches_app_prefix :
    forall full_hash depth prefix suffix,
      prefix_matches full_hash (depth + length suffix) (prefix ++ suffix) ->
      prefix_matches full_hash depth prefix.
  Proof.
    intros full_hash depth prefix suffix Hmatches.
    unfold prefix_matches in *. now apply prefix_matches_from_app_prefix with
      (suffix := suffix).
  Qed.

  Definition entry_matches (full_hash : N) (depth : nat) (prefix : list N)
      (entry : K * A) : Prop :=
    full_hash = hash seed (fst entry) /\
    (full_hash < hash_space)%N /\
    prefix_matches full_hash depth prefix.

  Inductive wf : nat -> list N -> tree K A -> Prop :=
  | wf_empty : forall depth prefix, wf depth prefix Empty
  | wf_leaf : forall depth prefix full_hash key value,
      full_hash = hash seed key ->
      (full_hash < hash_space)%N ->
      prefix_matches full_hash depth prefix ->
      wf depth prefix (Leaf full_hash key value)
  | wf_collision : forall depth prefix full_hash entries,
      2 <= length entries ->
      Forall (entry_matches full_hash depth prefix) entries ->
      NoDupA binding_equiv entries ->
      wf depth prefix (Collision full_hash entries)
  | wf_branch : forall depth prefix bitmap children,
      depth < branch_levels ->
      (bitmap < bitmap_limit)%N ->
      bitmap <> 0%N ->
      length children = popcount32 bitmap ->
      Forall2 (fun slot child => child <> Empty /\ wf (S depth) (prefix ++ [slot]) child)
        (occupied_slots bitmap) children ->
      NoDupA binding_equiv (bindings (Branch bitmap children)) ->
      wf depth prefix (Branch bitmap children).

Lemma wf_unary_branch :
    forall depth prefix full_hash (child : tree K A),
      depth < branch_levels ->
      child <> Empty ->
      wf (S depth) (prefix ++ [chunk full_hash depth]) child ->
      NoDupA binding_equiv (bindings child) ->
      wf depth prefix (Branch (child_bit full_hash depth) [child]).
Proof.
  intros depth prefix full_hash child Hdepth Hnonempty Hchild Hnodup.
  apply wf_branch.
  - exact Hdepth.
  - apply child_bit_bound.
  - apply child_bit_nonzero.
  - simpl. now rewrite child_bit_popcount.
  - unfold child_bit. rewrite (occupied_slots_bitmap_bit (slot := chunk full_hash depth)
      (chunk_bound full_hash depth)).
    constructor.
    + split; assumption.
    + constructor.
  - simpl. now rewrite app_nil_r.
Qed.

Lemma wf_leaf_descend :
    forall depth prefix full_hash key (value : A),
      length prefix = depth ->
      wf depth prefix (Leaf full_hash key value) ->
      wf (S depth) (prefix ++ [chunk full_hash depth])
        (Leaf full_hash key value).
Proof.
  intros depth prefix full_hash key value Hlength Hwf.
  inversion Hwf as [|d p h k v Hhash Hbound Hprefix| |]; subst.
  apply wf_leaf; auto.
  apply prefix_matches_append_slot; [reflexivity|exact Hprefix].
Qed.

Lemma wf_leaf_from_entry_descend :
    forall depth prefix full_hash key (value : A),
      length prefix = depth ->
      entry_matches full_hash depth prefix (key, value) ->
      wf (S depth) (prefix ++ [chunk full_hash depth])
        (Leaf full_hash key value).
Proof.
  intros depth prefix full_hash key value Hlength Hentry.
  destruct Hentry as [Hhash [Hbound Hprefix]].
  apply wf_leaf; auto.
  apply prefix_matches_append_slot; assumption.
Qed.

Lemma wf_collision_descend :
    forall depth prefix full_hash (entries : list (K * A)),
      length prefix = depth ->
      wf depth prefix (Collision full_hash entries) ->
      wf (S depth) (prefix ++ [chunk full_hash depth])
        (Collision full_hash entries).
Proof.
  intros depth prefix full_hash entries Hlength Hwf.
  inversion Hwf as [| |d p h es Hsize Hall Hnodup|]; subst.
  apply wf_collision; [exact Hsize| |exact Hnodup].
  clear Hwf Hsize Hnodup.
  induction Hall as [|entry entries Hentry Hall IH].
  - constructor.
  - destruct Hentry as [Hhash [Hbound Hprefix]]. constructor.
    + repeat split; auto.
      apply prefix_matches_append_slot; [reflexivity|exact Hprefix].
    + exact IH.
Qed.

Lemma wf_collision_hash_bound :
    forall depth prefix full_hash (entries : list (K * A)),
      wf depth prefix (Collision full_hash entries) ->
      (full_hash < hash_space)%N.
Proof.
  intros depth prefix full_hash entries Hwf.
  destruct entries as [|entry entries].
  - inversion Hwf as [| |d p h es Hsize Hall Hnodup|].
    simpl in Hsize. lia.
  - inversion Hwf as [| |d p h es Hsize Hall Hnodup|].
    apply Forall_forall with (x := entry) in Hall; [|now left].
    exact (proj1 (proj2 Hall)).
Qed.

Lemma wf_collision_prefix_matches :
    forall depth prefix full_hash (entries : list (K * A)),
      wf depth prefix (Collision full_hash entries) ->
      prefix_matches full_hash depth prefix.
Proof.
  intros depth prefix full_hash entries Hwf.
  destruct entries as [|entry entries].
  - inversion Hwf as [| |d p h es Hsize Hall Hnodup|].
    simpl in Hsize. lia.
  - inversion Hwf as [| |d p h es Hsize Hall Hnodup|].
    inversion Hall as [|head tail Hentry Htail]; subst.
    exact (proj2 (proj2 Hentry)).
Qed.

Lemma wf_join_worker_equal :
    forall fuel depth prefix left_hash right_hash (left right : tree K A),
      depth < branch_levels ->
      N.eqb (chunk left_hash depth) (chunk right_hash depth) = true ->
      let child := join_worker fuel (S depth) left_hash left right_hash right in
      child <> Empty ->
      wf (S depth) (prefix ++ [chunk left_hash depth]) child ->
      NoDupA binding_equiv (bindings child) ->
      wf depth prefix
        (join_worker (S fuel) depth left_hash left right_hash right).
Proof.
  intros fuel depth prefix left_hash right_hash left right Hdepth Hequal child
    Hnonempty Hchild Hnodup.
  cbn [join_worker]. rewrite Hequal.
  now apply wf_unary_branch.
Qed.

Lemma wf_join_worker_equal_recursive :
    forall fuel depth prefix left_hash right_hash (left right : tree K A),
      depth < branch_levels ->
      N.eqb (chunk left_hash depth) (chunk right_hash depth) = true ->
      wf (S depth) (prefix ++ [chunk left_hash depth])
        (join_worker fuel (S depth) left_hash left right_hash right) ->
      NoDupA binding_equiv
        (bindings (join_worker fuel (S depth) left_hash left right_hash right)) ->
      wf depth prefix
        (join_worker (S fuel) depth left_hash left right_hash right).
Proof.
  intros fuel depth prefix left_hash right_hash left right Hdepth Hequal Hchild Hnodup.
  eapply wf_join_worker_equal; eauto using join_worker_nonempty.
Qed.

Lemma wf_join_two :
 forall depth prefix left_hash right_hash (left right : tree K A),
 depth < branch_levels ->
 chunk left_hash depth <> chunk right_hash depth ->
 left <> Empty ->
 right <> Empty ->
 wf (S depth) (prefix ++ [chunk left_hash depth]) left ->
 wf (S depth) (prefix ++ [chunk right_hash depth]) right ->
 NoDupA binding_equiv (bindings (join_two left_hash left right_hash right depth)) ->
 wf depth prefix (join_two left_hash left right_hash right depth).
Proof.
 intros depth prefix left_hash right_hash left right Hdepth Hdifferent Hleftne Hrightne Hleft Hright Hnodup.
 unfold join_two in Hnodup.
 destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hlt.
 - unfold join_two. rewrite Hlt. apply wf_branch.
   + exact Hdepth.
   + apply join_two_bitmap_bound_total.
   + apply join_two_bitmap_nonzero.
   + change (2 = popcount32 (N.lor (bitmap_bit (chunk left_hash depth)) (bitmap_bit (chunk right_hash depth)))). rewrite popcount_lor_bitmap_bits.
     * reflexivity.
     * apply chunk_bound.
     * apply chunk_bound.
     * apply N.ltb_lt in Hlt. lia.
   + rewrite (occupied_slots_lor_bitmap_bits_lt (left := chunk left_hash depth) (right := chunk right_hash depth) (chunk_bound _ _) (chunk_bound _ _) Hlt).
     constructor; [split; [exact Hleftne|exact Hleft]|constructor; [split; [exact Hrightne|exact Hright]|constructor]].
   + exact Hnodup.
 - unfold join_two. rewrite Hlt. apply wf_branch.
   + exact Hdepth.
   + apply join_two_bitmap_bound_total.
   + apply join_two_bitmap_nonzero.
   + change (2 = popcount32 (N.lor (bitmap_bit (chunk left_hash depth)) (bitmap_bit (chunk right_hash depth)))). rewrite popcount_lor_bitmap_bits.
     * reflexivity.
     * apply chunk_bound.
     * apply chunk_bound.
     * exact Hdifferent.
   + assert (Hgt : N.ltb (chunk right_hash depth) (chunk left_hash depth) = true).
     { apply N.ltb_ge in Hlt. apply N.ltb_lt. apply (proj2 (N.le_neq _ _)). split; [exact Hlt|]. intro Heq. apply Hdifferent. exact (eq_sym Heq). }
     rewrite N.lor_comm. rewrite (occupied_slots_lor_bitmap_bits_lt (left := chunk right_hash depth) (right := chunk left_hash depth) (chunk_bound _ _) (chunk_bound _ _) Hgt).
     constructor; [split; [exact Hrightne|exact Hright]|constructor; [split; [exact Hleftne|exact Hleft]|constructor]].
   + exact Hnodup.
Qed.

Lemma wf_bindings_nodup :
  forall depth prefix (t : tree K A),
    wf depth prefix t ->
    NoDupA binding_equiv (bindings t).
Proof.
  intros depth prefix t Hwf. induction Hwf; simpl.
  - constructor.
  - constructor; [intro Hin; inversion Hin|constructor].
  - exact H1.
  - exact H4.
Qed.

Lemma forall2_slot_child_wf_early :
 forall depth prefix slots children,
 Forall2 (fun slot (child : tree K A) =>
   child <> Empty /\ wf (S depth) (prefix ++ [slot]) child) slots children ->
 forall slot, In slot slots ->
   exists child, In child children /\ child <> Empty /\
     wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix slots children Hpaired slot Hin.
 induction Hpaired.
 - contradiction.
 - simpl in Hin. destruct Hin as [Hslot|Hin].
   + subst slot. exists y. split; [now left|exact H].
   + destruct IHHpaired as [child [Hchild [Hnonempty Hwf]]]; auto.
     exists child. split; [now right|split; assumption].
Qed.

Lemma wf_nonempty_has_binding :
  forall (t : tree K A) depth prefix,
    wf depth prefix t ->
    t <> Empty ->
    exists entry, In entry (bindings t).
Proof.
  refine (@tree_ind_nested K A
    (fun t => forall depth prefix, wf depth prefix t -> t <> Empty ->
      exists entry, In entry (bindings t))
    _ _ _ _).
  - intros depth prefix Hwf Hnonempty. contradiction.
  - intros full_hash key value depth prefix Hwf Hnonempty.
    exists (key, value). now left.
  - intros full_hash entries depth prefix Hwf Hnonempty.
    destruct entries as [|entry entries].
    + inversion Hwf as [| |d p h es Hlength Hentries Hnodup|]; simpl in Hlength.
      lia.
    + exists entry. now left.
  - intros bitmap children IH depth prefix Hwf Hnonempty.
    inversion Hwf as [| | |d p b cs Hdepth Hbound Hbitmap_nonzero Hlength
      Hchildren Hnodup]; subst.
    destruct (@bitmap_nonzero_has_slot bitmap Hbound Hbitmap_nonzero)
      as [slot [Hslot_bound Hslot_has]].
    assert (Hslot_in : In slot (occupied_slots bitmap)).
    { now apply occupied_slots_complete. }
    destruct (forall2_slot_child_wf_early (depth := depth) prefix Hchildren slot Hslot_in)
      as [child [Hchild_in [Hchild_nonempty Hchild_wf]]].
    pose proof ((proj1 (Forall_forall _ _)) IH child Hchild_in) as Hih.
    destruct (Hih (S depth) (prefix ++ [slot]) Hchild_wf Hchild_nonempty)
      as [entry Hentry].
    exists entry. simpl. apply in_flat_map.
    now exists child.
Qed.

Lemma wf_branch_children_occupied_length :
  forall depth prefix bitmap children,
    wf depth prefix (Branch bitmap children) ->
    length children = length (occupied_slots bitmap).
Proof.
  intros depth prefix bitmap children Hwf.
  inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Hnodup];
    subst.
  rewrite Hlength, occupied_slots_length_popcount. reflexivity.
Qed.

Lemma wf_join_worker_equal_wf :
    forall fuel depth prefix left_hash right_hash (left right : tree K A),
      depth < branch_levels ->
      N.eqb (chunk left_hash depth) (chunk right_hash depth) = true ->
      wf (S depth) (prefix ++ [chunk left_hash depth])
        (join_worker fuel (S depth) left_hash left right_hash right) ->
      wf depth prefix
        (join_worker (S fuel) depth left_hash left right_hash right).
Proof.
  intros fuel depth prefix left_hash right_hash left right Hdepth Hequal Hchild.
  apply wf_join_worker_equal_recursive with
    (fuel := fuel) (left_hash := left_hash) (right_hash := right_hash);
    auto.
  apply wf_bindings_nodup with (depth := S depth)
    (prefix := prefix ++ [chunk left_hash depth]). exact Hchild.
Qed.

Lemma forall2_child_wf :
 forall depth prefix slots children,
 Forall2 (fun slot (child : tree K A) =>
   child <> Empty /\ wf (S depth) (prefix ++ [slot]) child) slots children ->
 forall child, In child children ->
   exists slot, child <> Empty /\ wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix slots children Hpaired child Hin. induction Hpaired.
 - contradiction.
 - simpl in Hin. destruct Hin as [->|Hin].
   + exists x. exact H.
   + apply IHHpaired. exact Hin.
Qed.

Lemma forall2_child_wf_in :
 forall depth prefix slots children,
 Forall2 (fun slot (child : tree K A) =>
   child <> Empty /\ wf (S depth) (prefix ++ [slot]) child) slots children ->
 forall child, In child children ->
   exists slot, In slot slots /\ child <> Empty /\
     wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix slots children Hpaired child Hin.
 induction Hpaired.
 - contradiction.
 - simpl in Hin. destruct Hin as [->|Hin].
   + exists x. split; [now left|exact H].
   + destruct IHHpaired as [slot [Hslot [Hnonempty Hwf]]]; auto.
     exists slot. split; [now right|split; assumption].
Qed.

Lemma forall2_slot_child_wf :
 forall depth prefix slots children,
 Forall2 (fun slot (child : tree K A) =>
   child <> Empty /\ wf (S depth) (prefix ++ [slot]) child) slots children ->
 forall slot, In slot slots ->
   exists child, In child children /\ child <> Empty /\
     wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix slots children Hpaired slot Hin.
 induction Hpaired as [|head_slot head_child slots children Hhead Htail IH].
 - contradiction.
 - simpl in Hin. destruct Hin as [Hslot|Hin].
   + subst head_slot. exists head_child. simpl. tauto.
   + destruct (IH Hin) as [child [Hchild [Hnonempty Hwf]]].
     exists child. simpl. tauto.
Qed.

Lemma forall2_nth :
 forall X Y (R : X -> Y -> Prop) slots children index slot,
 Forall2 R slots children ->
 nth_error slots index = Some slot ->
 exists child, nth_error children index = Some child /\ R slot child.
Proof.
 intros X Y R slots children index slot Hpaired Hslot.
 revert index slot Hslot.
 induction Hpaired as [|head_slot head_child slots children Hhead Htail IH];
   intros index slot Hslot.
 - destruct index; discriminate.
 - destruct index as [|index].
   + simpl in Hslot. inversion Hslot; subst slot.
     exists head_child. split; [reflexivity|exact Hhead].
   + simpl in Hslot. eapply IH; eauto.
Qed.

Lemma wf_branch_depth :
 forall depth prefix bitmap children,
 wf depth prefix (Branch bitmap children) -> depth < branch_levels.
Proof.
 intros depth prefix bitmap children Hwf.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Hnodup];
   exact Hdepth.
Qed.

Lemma wf_branch_impossible_at_or_beyond_limit :
 forall depth prefix bitmap children,
 branch_levels <= depth ->
 wf depth prefix (Branch bitmap children) -> False.
Proof.
 intros depth prefix bitmap children Hlimit Hwf.
 pose proof (wf_branch_depth Hwf). lia.
Qed.

Lemma wf_branch_child :
 forall depth prefix bitmap children child,
 wf depth prefix (Branch bitmap children) ->
 In child children ->
 exists slot, child <> Empty /\
   wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix bitmap children child Hwf Hin.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Hnodup];
   subst.
 eapply forall2_child_wf; eauto.
Qed.

Lemma wf_branch_occupied_child :
 forall depth prefix bitmap children slot,
 wf depth prefix (Branch bitmap children) ->
 In slot (occupied_slots bitmap) ->
 exists child, In child children /\ child <> Empty /\
   wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix bitmap children slot Hwf Hin.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Hnodup];
   subst.
 eapply forall2_slot_child_wf; eauto.
Qed.

Lemma wf_branch_bitmap_child :
 forall depth prefix bitmap children slot,
 wf depth prefix (Branch bitmap children) ->
 (slot < branch_width)%N ->
 bitmap_has bitmap slot = true ->
 exists child, In child children /\ child <> Empty /\
   wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix bitmap children slot Hwf Hslot Hhas.
 apply wf_branch_occupied_child with (bitmap := bitmap).
 - exact Hwf.
  - now apply occupied_slots_complete.
Qed.

Lemma wf_branch_ranked_child :
 forall depth prefix bitmap children slot,
 wf depth prefix (Branch bitmap children) ->
 (slot < branch_width)%N ->
 bitmap_has bitmap slot = true ->
 exists child,
 dense_get (rank bitmap slot) children = Some child /\ child <> Empty /\
   wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix bitmap children slot Hwf Hslot Hhas.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Hnodup];
   subst.
 destruct (@occupied_slots_rank_split_N slot bitmap Hslot Hhas)
   as [before [after [Hslots Hrank]]].
 assert (Hnth : nth_error (occupied_slots bitmap) (rank bitmap slot) = Some slot).
 { rewrite Hslots, <- Hrank.
   rewrite nth_error_app2 by lia.
   replace (length before - length before) with 0 by lia.
   reflexivity. }
 destruct (forall2_nth (rank bitmap slot) Hchildren Hnth)
   as [child [Hchild Hrelated]].
 exists child. split.
 - exact Hchild.
  - exact Hrelated.
Qed.

Fixpoint get_tree_falls_back {K A : Type} (fuel depth : nat)
    (full_hash : N) (t : tree K A) : bool :=
  match fuel, t with
  | 0, Branch _ _ => true
  | S fuel', Branch bitmap children =>
      if bitmap_has bitmap (chunk full_hash depth) then
        match dense_get (rank bitmap (chunk full_hash depth)) children with
        | Some child => get_tree_falls_back fuel' (S depth) full_hash child
        | None => false
        end
      else false
  | _, _ => false
  end.

Lemma get_tree_wf_no_fallback :
 forall fuel depth prefix full_hash (t : tree K A),
   fuel + depth = branch_levels ->
   wf depth prefix t ->
   get_tree_falls_back fuel depth full_hash t = false.
Proof.
 induction fuel as [|fuel IH]; intros depth prefix full_hash t Hfuel Hwf;
   destruct t as [|stored_hash stored value|stored_hash entries|bitmap children];
   cbn [get_tree_falls_back].
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - assert (Hlimit : branch_levels <= depth) by lia.
   exfalso. apply (wf_branch_impossible_at_or_beyond_limit Hlimit Hwf).
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent;
     [destruct (@wf_branch_ranked_child depth prefix bitmap children
        (chunk full_hash depth) Hwf (chunk_bound full_hash depth) Hpresent)
       as [child [Hchild [_ Hchildwf]]]
     |reflexivity].
   rewrite Hchild.
   assert (Hnext : fuel + S depth = branch_levels) by lia.
   exact (IH (S depth) (prefix ++ [chunk full_hash depth]) full_hash child
     Hnext Hchildwf).
Qed.

Definition set_tree_falls_back {K A : Type} (fuel depth : nat)
    (full_hash : N) (t : tree K A) : bool :=
  get_tree_falls_back fuel depth full_hash t.

Lemma set_tree_wf_no_fallback :
 forall fuel depth prefix full_hash (t : tree K A),
   fuel + depth = branch_levels ->
   wf depth prefix t ->
   set_tree_falls_back fuel depth full_hash t = false.
Proof. exact get_tree_wf_no_fallback. Qed.

Definition remove_tree_falls_back {K A : Type} (fuel depth : nat)
    (full_hash : N) (t : tree K A) : bool :=
  get_tree_falls_back fuel depth full_hash t.

Lemma remove_tree_wf_no_fallback :
 forall fuel depth prefix full_hash (t : tree K A),
   fuel + depth = branch_levels ->
   wf depth prefix t ->
   remove_tree_falls_back fuel depth full_hash t = false.
Proof. exact get_tree_wf_no_fallback. Qed.

Lemma wf_branch_replace :
 forall depth prefix bitmap children slot (child : tree K A),
 wf depth prefix (Branch bitmap children) ->
 (slot < branch_width)%N ->
 bitmap_has bitmap slot = true ->
 child <> Empty ->
 wf (S depth) (prefix ++ [slot]) child ->
 NoDupA binding_equiv
   (bindings (branch_replace bitmap slot child children)) ->
 wf depth prefix (branch_replace bitmap slot child children).
Proof.
 intros depth prefix bitmap children slot child Hwf Hslot Hpresent Hnonempty
   Hchild Hnodup.
 destruct (wf_branch_ranked_child Hwf Hslot Hpresent)
   as [old_child [Hget [Holdnonempty Holdwf]]].
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Holdnodup];
   subst.
 assert (Hindex : rank bitmap slot < length children).
 { apply (proj1 (nth_error_Some children (rank bitmap slot))).
   unfold dense_get in Hget. rewrite Hget. discriminate. }
 assert (Hnth : nth_error (occupied_slots bitmap) (rank bitmap slot) = Some slot).
 { destruct (@occupied_slots_rank_split_N slot bitmap Hslot Hpresent)
     as [before [after [Hslots Hrank]]].
   rewrite Hslots, <- Hrank.
   rewrite nth_error_app2 by lia.
   replace (length before - length before) with 0 by lia.
   reflexivity. }
 unfold branch_replace. apply wf_branch.
 - exact Hdepth.
 - exact Hbound.
 - exact Hnonzero.
 - rewrite dense_replace_length. exact Hlength.
 - eapply Forall2_dense_replace.
   + exact Hchildren.
   + exact Hindex.
   + intros routed old Hroute Hold.
     rewrite Hnth in Hroute. inversion Hroute; subst routed.
     split; assumption.
 - exact Hnodup.
Qed.

Lemma wf_branch_insert :
 forall depth prefix bitmap children slot (child : tree K A),
 wf depth prefix (Branch bitmap children) ->
 (slot < branch_width)%N ->
 bitmap_has bitmap slot = false ->
 child <> Empty ->
 wf (S depth) (prefix ++ [slot]) child ->
 (N.lor bitmap (bitmap_bit slot) < bitmap_limit)%N ->
 popcount32 (N.lor bitmap (bitmap_bit slot)) = S (popcount32 bitmap) ->
 Forall2 (fun routed inserted => inserted <> Empty /\
   wf (S depth) (prefix ++ [routed]) inserted)
   (occupied_slots (N.lor bitmap (bitmap_bit slot)))
   (dense_insert (rank bitmap slot) child children) ->
 NoDupA binding_equiv (bindings (branch_insert bitmap slot child children)) ->
 wf depth prefix (branch_insert bitmap slot child children).
Proof.
 intros depth prefix bitmap children slot child Hwf Hslot Habsent Hnonempty
   Hchild Hbound Hpop Hchildren Hnodup.
 inversion Hwf as [| | |d p b cs Hdepth Holdbound Holdnonzero Hlength
   Holdchildren Holdnodup]; subst.
 unfold branch_insert. apply wf_branch.
 - exact Hdepth.
 - exact Hbound.
 - intro Hzero.
   assert (Hhas : bitmap_has (N.lor bitmap (bitmap_bit slot)) slot = true).
   { apply bitmap_has_lor_right.
     now apply bitmap_bit_has_slot. }
   rewrite Hzero, bitmap_has_empty in Hhas. discriminate.
 - rewrite dense_insert_length, Hlength, Hpop. reflexivity.
 - exact Hchildren.
 - exact Hnodup.
Qed.

Lemma wf_branch_insert_absent :
 forall depth prefix bitmap children slot (child : tree K A),
 wf depth prefix (Branch bitmap children) ->
 (slot < branch_width)%N ->
 bitmap_has bitmap slot = false ->
 child <> Empty ->
 wf (S depth) (prefix ++ [slot]) child ->
 NoDupA binding_equiv (bindings (branch_insert bitmap slot child children)) ->
 wf depth prefix (branch_insert bitmap slot child children).
Proof.
 intros depth prefix bitmap children slot child Hwf Hslot Habsent Hnonempty
   Hchild Hnodup.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren
   Holdnodup]; subst.
 destruct (@occupied_slots_lor_bit_absent_split bitmap slot Hslot Habsent)
   as [before [after [Hslots [Hrank Hnew]]]].
 rewrite Hslots in Hchildren.
 destruct (@Forall2_app_inv_l N (tree K A)
   (fun routed inserted => inserted <> Empty /\
     wf (S depth) (prefix ++ [routed]) inserted)
   before after children Hchildren)
   as [children_before [children_after
     [Hbefore [Hafter Hchildren_eq]]]].
 unfold branch_insert. apply wf_branch.
 - exact Hdepth.
 - now apply bitmap_lor_bit_bound_absent.
 - intro Hzero.
   assert (Hpresent : bitmap_has (N.lor bitmap (bitmap_bit slot)) slot = true).
   { apply bitmap_has_lor_right. apply bitmap_bit_has_slot. }
   rewrite Hzero, bitmap_has_empty in Hpresent. discriminate.
 - rewrite dense_insert_length, Hlength.
   symmetry. now apply popcount_lor_bit_absent.
 - assert (Hbefore_length : length children_before = length before).
   { symmetry. exact (@Forall2_length N (tree K A)
       (fun routed inserted => inserted <> Empty /\
         wf (S depth) (prefix ++ [routed]) inserted)
       before children_before Hbefore). }
   rewrite Hnew, Hchildren_eq, <- Hrank, <- Hbefore_length.
   apply Forall2_dense_insert; try assumption.
   split; assumption.
 - exact Hnodup.
Qed.

Inductive branch_path_depth : tree K A -> nat -> Prop :=
| branch_path_here : forall bitmap children,
    branch_path_depth (Branch bitmap children) 0
| branch_path_child : forall bitmap children child steps,
    In child children ->
    branch_path_depth child steps ->
    branch_path_depth (Branch bitmap children) (S steps).

Lemma wf_branch_path_bound :
 forall depth prefix (t : tree K A) steps,
 wf depth prefix t ->
 branch_path_depth t steps ->
 depth + steps < branch_levels.
Proof.
 intros depth prefix t steps Hwf Hpath.
 revert depth prefix Hwf.
 induction Hpath as [bitmap children|bitmap children child steps Hin Hpath IH];
   intros depth prefix Hwf.
 - pose proof (wf_branch_depth Hwf). lia.
 - inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren Hnodup];
     subst.
   assert (Hchild_details : exists slot, child <> Empty /\
     wf (S depth) (prefix ++ [slot]) child).
   { eapply forall2_child_wf; eauto. }
   destruct Hchild_details as [slot [Hnonempty Hchild]].
   specialize (IH (S depth) (prefix ++ [slot]) Hchild). lia.
Qed.

Lemma wf_binding_hash :
 forall (t : tree K A) depth prefix, wf depth prefix t ->
 forall entry, In entry (bindings t) ->
 exists full_hash,
   full_hash = hash seed (fst entry) /\ (full_hash < hash_space)%N.
Proof.
 refine (@tree_ind_nested K A
   (fun t => forall depth prefix, wf depth prefix t -> forall entry,
      In entry (bindings t) -> exists full_hash,
        full_hash = hash seed (fst entry) /\ (full_hash < hash_space)%N)
   _ _ _ _).
 - intros depth prefix Hwf entry Hin. contradiction.
 - intros stored_hash key value depth prefix Hwf entry Hin.
   simpl in Hin. destruct Hin as [Heq|[]]. subst entry.
   inversion Hwf as [|d p h k v Hhash Hbound Hprefix| |]; subst.
   exists (hash seed key). simpl. auto.
 - intros stored_hash entries depth prefix Hwf entry Hin.
   inversion Hwf; subst. change (In entry entries) in Hin.
   apply Forall_forall with (x := entry) in H4; auto.
   destruct H4 as [Hhash [Hbound _]]. exists stored_hash. auto.
 - intros bitmap children IH depth prefix Hwf entry Hin.
   inversion Hwf as [| | | depth' prefix' bitmap' children' Hd Hb Hn Hl Hp Hdup];
     subst.
   simpl in Hin. apply in_flat_map in Hin.
   destruct Hin as [child [Hchild Hin]].
   destruct (forall2_child_wf (depth := depth) prefix Hp child Hchild)
     as [slot [_ Hwfchild]].
   apply Forall_forall with (x := child) in IH; auto.
   exact (IH (S depth) (prefix ++ [slot]) Hwfchild entry Hin).
Qed.

Lemma wf_binding_prefix_matches :
 forall (t : tree K A) depth prefix,
   length prefix = depth -> wf depth prefix t ->
 forall entry, In entry (bindings t) ->
   prefix_matches (hash seed (fst entry)) depth prefix.
Proof.
 refine (@tree_ind_nested K A
   (fun t => forall depth prefix, length prefix = depth -> wf depth prefix t ->
      forall entry, In entry (bindings t) ->
        prefix_matches (hash seed (fst entry)) depth prefix)
   _ _ _ _).
 - intros depth prefix Hlength Hwf entry Hin. contradiction.
 - intros stored_hash key value depth prefix Hlength Hwf entry Hin.
   simpl in Hin. destruct Hin as [Heq|[]]. subst entry.
   inversion Hwf; subst; eauto 3.
 - intros stored_hash entries depth prefix Hlength Hwf entry Hin.
   inversion Hwf; subst.
   match goal with
   | Hentries : Forall _ _ |- _ =>
       apply Forall_forall with (x := entry) in Hentries; auto;
       destruct Hentries as [Hhash [_ Hprefix]]; now rewrite <- Hhash
   end.
 - intros bitmap children IH depth prefix Hlength Hwf entry Hin.
   inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hchildren_len
     Hchildren Hnodup].
   simpl in Hin. apply in_flat_map in Hin.
   destruct Hin as [child [Hchild Hin]].
   destruct (forall2_child_wf (depth := depth) prefix Hchildren child Hchild)
     as [slot [_ Hchildwf]].
   pose proof ((proj1 (Forall_forall _ _)) IH child Hchild) as Hih.
   assert (Hchild_length : length (prefix ++ [slot]) = S depth).
   { rewrite app_length, Hlength. simpl. lia. }
   specialize (Hih (S depth) (prefix ++ [slot]) Hchild_length Hchildwf entry Hin).
   + apply prefix_matches_app_prefix with (suffix := [slot]).
     exact Hih.
Qed.

Lemma wf_branch_binding_routes :
 forall depth prefix bitmap children,
   length prefix = depth ->
   wf depth prefix (Branch bitmap children) ->
 forall entry, In entry (bindings (Branch bitmap children)) ->
   bitmap_has bitmap (chunk (hash seed (fst entry)) depth) = true.
Proof.
 intros depth prefix bitmap children Hlength Hwf entry Hin.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hchildren_len
   Hchildren Hnodup].
 simpl in Hin. apply in_flat_map in Hin.
 destruct Hin as [child [Hchild Hin]].
 destruct (forall2_child_wf_in (depth := depth) prefix Hchildren child Hchild)
   as [slot [Hslot_in [_ Hchildwf]]].
 assert (Hprefix : prefix_matches (hash seed (fst entry)) (S depth)
     (prefix ++ [slot])).
 { apply wf_binding_prefix_matches with (t := child).
   - rewrite app_length, Hlength. simpl. lia.
   - exact Hchildwf.
   - exact Hin. }
 assert (Hslot : chunk (hash seed (fst entry)) depth = slot).
 { unfold prefix_matches in Hprefix.
   pose proof (prefix_matches_from_app_last
     (hash seed (fst entry)) 0 prefix slot Hprefix) as Hroute.
   replace (0 + length prefix) with depth in Hroute by lia.
   exact Hroute. }
 rewrite Hslot.
 apply occupied_slots_sound.
 exact Hslot_in.
Qed.

Lemma wf_branch_child_binding_slot :
 forall depth prefix bitmap children (child : tree K A) entry,
   length prefix = depth ->
   wf depth prefix (Branch bitmap children) ->
   In child children ->
   In entry (bindings child) ->
   exists slot,
     In slot (occupied_slots bitmap) /\
     chunk (hash seed (fst entry)) depth = slot /\
     wf (S depth) (prefix ++ [slot]) child.
Proof.
 intros depth prefix bitmap children child entry Hlength Hwf Hchild Hin.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hchildren_len
   Hchildren Hnodup].
 destruct (forall2_child_wf_in (depth := depth) prefix Hchildren child Hchild)
   as [slot [Hslot [Hnonempty Hchildwf]]].
 exists slot. split; [exact Hslot|]. split; [|exact Hchildwf].
 assert (Hprefix : prefix_matches (hash seed (fst entry)) (S depth)
   (prefix ++ [slot])).
 { eapply wf_binding_prefix_matches.
   - rewrite app_length, Hlength. cbn. lia.
   - exact Hchildwf.
   - exact Hin. }
 unfold prefix_matches in Hprefix.
 pose proof (prefix_matches_from_app_last
   (hash seed (fst entry)) 0 prefix slot Hprefix) as Hroute.
 replace (0 + length prefix) with depth in Hroute by lia.
 exact Hroute.
Qed.

Lemma Forall2_dense_get_split_early :
  forall X Y (R : X -> Y -> Prop) index slots children slot child,
    Forall2 R slots children ->
    nth_error slots index = Some slot ->
    dense_get index children = Some child ->
    exists slots_before slots_after children_before children_after,
      slots = slots_before ++ slot :: slots_after /\
      children = children_before ++ child :: children_after /\
      length slots_before = index /\
      Forall2 R slots_before children_before /\
      R slot child /\
      Forall2 R slots_after children_after.
Proof.
  intros X Y R index. induction index as [|index IH];
    intros slots children slot child Hpaired Hslot Hchild;
    destruct slots as [|head_slot slots]; destruct children as [|head_child children].
  - discriminate.
  - inversion Hpaired.
  - inversion Hpaired.
  - inversion Hpaired as [|slot' child' slots' children' Hhead Htail]; subst.
    simpl in Hslot, Hchild. inversion Hslot; inversion Hchild; subst.
    exists [], slots, [], children. simpl. repeat split; auto.
  - discriminate.
  - inversion Hpaired.
  - inversion Hpaired.
  - inversion Hpaired as [|slot' child' slots' children' Hhead Htail]; subst.
    simpl in Hslot, Hchild.
    destruct (IH slots children slot child Htail Hslot Hchild)
      as [slots_before [slots_after [children_before [children_after
        [Hslots [Hchildren [Hlength [Hbefore [Hselected Hafter]]]]]]]]].
    exists (head_slot :: slots_before), slots_after,
      (head_child :: children_before), children_after.
    simpl. rewrite Hslots, Hchildren. repeat split; try reflexivity;
      try (simpl; lia).
    + constructor; assumption.
    + exact Hselected.
    + exact Hafter.
Qed.

Lemma NoDup_before_selected_early :
  forall X (before after : list X) selected candidate,
    NoDup (before ++ selected :: after) ->
    In candidate before -> selected <> candidate.
Proof.
  intros X before. induction before as [|head before IH];
    intros after selected candidate Hnodup Hin.
  - contradiction.
  - simpl in Hin. inversion Hnodup as [|head' tail Hfresh Htail]; subst.
    destruct Hin as [Hcandidate|Hin].
    + subst candidate. intro Heq. subst selected.
      apply Hfresh. apply in_app_iff. right. now left.
    + apply IH with (after := after); assumption.
Qed.

Lemma NoDup_after_selected_early :
  forall X (before after : list X) selected candidate,
    NoDup (before ++ selected :: after) ->
    In candidate after -> selected <> candidate.
Proof.
  intros X before after selected candidate Hnodup Hin Heq. subst candidate.
  apply NoDup_app_remove_l with (l := before) in Hnodup.
  inversion Hnodup as [|selected' after' Hfresh Htail]; subst.
  apply Hfresh. exact Hin.
Qed.

Lemma wf_branch_dense_get_binding :
 forall depth prefix bitmap children slot (child : tree K A) entry,
   length prefix = depth ->
   wf depth prefix (Branch bitmap children) ->
   bitmap_has bitmap slot = true ->
   dense_get (rank bitmap slot) children = Some child ->
   In entry (bindings (Branch bitmap children)) ->
   chunk (hash seed (fst entry)) depth = slot ->
   In entry (bindings child).
Proof.
 intros depth prefix bitmap children slot child entry Hlength Hwf Hpresent Hget
   Hin Hroute.
 pose proof Hwf as Hwf_original.
 inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hchildren_len
   Hchildren Hnodup].
 assert (Hslot_bound : (slot < branch_width)%N).
 { rewrite <- Hroute. apply chunk_bound. }
 destruct (@occupied_slots_rank_split_N slot bitmap Hslot_bound Hpresent)
   as [slots_before [slots_after [Hslots Hrank]]].
 assert (Hnth : nth_error (occupied_slots bitmap) (rank bitmap slot) = Some slot).
 { rewrite Hslots, <- Hrank.
   rewrite nth_error_app2 by lia.
   replace (length slots_before - length slots_before) with 0 by lia.
   reflexivity. }
 destruct (@Forall2_dense_get_split_early N (tree K A)
   (fun routed selected => selected <> Empty /\
      wf (S depth) (prefix ++ [routed]) selected)
   (rank bitmap slot) (occupied_slots bitmap) children slot child Hchildren Hnth Hget)
   as [split_slots_before [split_slots_after
     [children_before [children_after
       [Hslots_split [Hchildren_split [Hbefore [Hselected Hafter]]]]]]]].
 destruct Hafter as [Hselected_pair Hafter].
 assert (Hslots_nodup : NoDup (occupied_slots bitmap)).
 { apply occupied_slots_nodup. }
 change (In entry (flat_map bindings children)) in Hin.
 rewrite Hchildren_split in Hin.
 repeat rewrite flat_map_app in Hin. simpl in Hin.
 repeat rewrite in_app_iff in Hin.
 destruct Hin as [Hinbefore|[Hinchild|Hinafter]].
 - exfalso.
   apply in_flat_map in Hinbefore.
   destruct Hinbefore as [other [Hotherbefore Hentry]].
   destruct (forall2_child_wf_in (depth := depth) prefix Hselected other Hotherbefore)
       as [routed [Hrouted [Hothernonempty Hotherwf']]].
   assert (Hother_route : chunk (hash seed (fst entry)) depth = routed).
   { assert (Hotherprefix : prefix_matches (hash seed (fst entry)) (S depth)
       (prefix ++ [routed])).
     { eapply wf_binding_prefix_matches.
       - rewrite app_length, Hlength. cbn. lia.
       - exact Hotherwf'.
       - exact Hentry. }
     unfold prefix_matches in Hotherprefix.
     pose proof (prefix_matches_from_app_last
       (hash seed (fst entry)) 0 prefix routed Hotherprefix) as Hroute'.
     replace (0 + length prefix) with depth in Hroute' by lia.
     exact Hroute'. }
   assert (Hdifferent : slot <> routed).
   { rewrite Hslots_split in Hslots_nodup.
     apply NoDup_before_selected_early with (before := split_slots_before)
       (after := split_slots_after); assumption. }
   apply Hdifferent. rewrite <- Hroute, <- Hother_route. reflexivity.
 - exact Hinchild.
 - exfalso.
   apply in_flat_map in Hinafter.
   destruct Hinafter as [other [Hotherafter Hentry]].
   destruct (forall2_child_wf_in (depth := depth) prefix Hafter other Hotherafter)
       as [routed [Hrouted [Hothernonempty Hotherwf']]].
   assert (Hother_route : chunk (hash seed (fst entry)) depth = routed).
   { assert (Hotherprefix : prefix_matches (hash seed (fst entry)) (S depth)
       (prefix ++ [routed])).
     { eapply wf_binding_prefix_matches.
       - rewrite app_length, Hlength. cbn. lia.
       - exact Hotherwf'.
       - exact Hentry. }
     unfold prefix_matches in Hotherprefix.
     pose proof (prefix_matches_from_app_last
       (hash seed (fst entry)) 0 prefix routed Hotherprefix) as Hroute'.
     replace (0 + length prefix) with depth in Hroute' by lia.
     exact Hroute'. }
   assert (Hdifferent : slot <> routed).
   { rewrite Hslots_split in Hslots_nodup.
     apply NoDup_after_selected_early with (before := split_slots_before)
       (after := split_slots_after); assumption. }
   apply Hdifferent. rewrite <- Hroute, <- Hother_route. reflexivity.
Qed.

Lemma collision_binding_hash :
 forall depth prefix full_hash (entries : list (K * A)) (entry : K * A),
 wf depth prefix (Collision full_hash entries) ->
 In entry entries -> full_hash = hash seed (fst entry).
Proof.
 intros depth prefix full_hash entries entry Hwf Hin.
 inversion Hwf as [| | d p h es Hlen Hall Hnodup|]; subst.
 apply Forall_forall with (x := entry) in Hall; auto.
 exact (proj1 Hall).
Qed.

Lemma binding_equiv_equiv :
 Equivalence E -> Equivalence (fun (left right : K * A) =>
   E (fst left) (fst right)).
Proof.
 intros [Href Hsym Htrans]. split.
 - intro entry. unfold binding_equiv. apply Href.
 - intros left right Hleft. unfold binding_equiv in *. apply Hsym. exact Hleft.
 - intros left middle right Hleft Hright. unfold binding_equiv in *.
   eapply Htrans; eauto.
Qed.

Lemma inA_witness :
 forall (R : (K * A) -> (K * A) -> Prop) entry entries,
 InA R entry entries -> exists stored, In stored entries /\ R entry stored.
Proof.
 intros R entry entries Hin. induction Hin.
 - exists y. split; [now left|assumption].
 - destruct IHHin as [stored [Hstored HR]]. exists stored.
   split; [now right|assumption].
Qed.

Lemma wf_branch_slot_absent_fresh :
 forall depth prefix bitmap children full_hash key (value : A),
   Equivalence E ->
   (forall first second, E first second ->
     hash seed first = hash seed second) ->
   length prefix = depth ->
   full_hash = hash seed key ->
   wf depth prefix (Branch bitmap children) ->
   bitmap_has bitmap (chunk full_hash depth) = false ->
   ~ InA binding_equiv (key, value) (bindings (Branch bitmap children)).
Proof.
 intros depth prefix bitmap children full_hash key value Hequiv Hcongruent
   Hlength Hhash Hwf Habsent Hin.
 destruct (inA_witness Hin) as [entry [Hentry Hrelated]].
 assert (Hroute : bitmap_has bitmap
   (chunk (hash seed (fst entry)) depth) = true).
 { eapply wf_branch_binding_routes.
   - exact Hlength.
   - exact Hwf.
   - exact Hentry. }
 assert (Hsame : full_hash = hash seed (fst entry)).
 { rewrite Hhash. apply Hcongruent. exact Hrelated. }
 rewrite <- Hsame in Hroute.
 now rewrite Habsent in Hroute.
Qed.

Lemma wf_sibling_bindings_disjoint :
 forall depth prefix left_slot right_slot (left right : tree K A),
   Equivalence E ->
   (forall first second, E first second ->
     hash seed first = hash seed second) ->
   length prefix = depth ->
   left_slot <> right_slot ->
   wf (S depth) (prefix ++ [left_slot]) left ->
   wf (S depth) (prefix ++ [right_slot]) right ->
 forall entry, InA binding_equiv entry (bindings left) ->
   InA binding_equiv entry (bindings right) -> False.
Proof.
 intros depth prefix left_slot right_slot left right Hequiv Hcongruent Hlength
   Hslots Hleft Hright entry Hinleft Hinright.
 destruct (inA_witness Hinleft)
   as [left_entry [Hleft_entry Hleft_related]].
 destruct (inA_witness Hinright)
   as [right_entry [Hright_entry Hright_related]].
 assert (Hleft_prefix : prefix_matches (hash seed (fst left_entry))
   (S depth) (prefix ++ [left_slot])).
 { eapply wf_binding_prefix_matches.
   - rewrite app_length, Hlength. simpl. lia.
   - exact Hleft.
   - exact Hleft_entry. }
 assert (Hright_prefix : prefix_matches (hash seed (fst right_entry))
   (S depth) (prefix ++ [right_slot])).
 { eapply wf_binding_prefix_matches.
   - rewrite app_length, Hlength. simpl. lia.
   - exact Hright.
   - exact Hright_entry. }
 assert (Hleft_slot : chunk (hash seed (fst left_entry)) depth = left_slot).
 { unfold prefix_matches in Hleft_prefix.
   pose proof (prefix_matches_from_app_last
     (hash seed (fst left_entry)) 0 prefix left_slot Hleft_prefix) as Hslot.
   replace (0 + length prefix) with depth in Hslot by lia.
   exact Hslot. }
 assert (Hright_slot : chunk (hash seed (fst right_entry)) depth = right_slot).
 { unfold prefix_matches in Hright_prefix.
   pose proof (prefix_matches_from_app_last
     (hash seed (fst right_entry)) 0 prefix right_slot Hright_prefix) as Hslot.
   replace (0 + length prefix) with depth in Hslot by lia.
   exact Hslot. }
 apply Hslots. rewrite <- Hleft_slot, <- Hright_slot.
 rewrite <- (Hcongruent (fst entry) (fst left_entry) Hleft_related).
 rewrite <- (Hcongruent (fst entry) (fst right_entry) Hright_related).
 reflexivity.
Qed.

Lemma wf_sibling_key_fresh :
 forall depth prefix selected_slot sibling_slot (sibling : tree K A)
        full_hash key (value : A),
   (forall first second, E first second ->
     hash seed first = hash seed second) ->
   length prefix = depth ->
   selected_slot <> sibling_slot ->
   full_hash = hash seed key ->
   chunk full_hash depth = selected_slot ->
   wf (S depth) (prefix ++ [sibling_slot]) sibling ->
   ~ InA binding_equiv (key, value) (bindings sibling).
Proof.
 intros depth prefix selected_slot sibling_slot sibling full_hash key value
   Hcongruent Hlength Hslots Hhash Hroute Hwf Hin.
 destruct (inA_witness Hin)
   as [entry [Hentry Hrelated]].
 assert (Hprefix : prefix_matches (hash seed (fst entry)) (S depth)
   (prefix ++ [sibling_slot])).
 { eapply wf_binding_prefix_matches.
   - rewrite app_length, Hlength. simpl. lia.
   - exact Hwf.
   - exact Hentry. }
 assert (Hsibling : chunk (hash seed (fst entry)) depth = sibling_slot).
 { unfold prefix_matches in Hprefix.
   pose proof (prefix_matches_from_app_last
     (hash seed (fst entry)) 0 prefix sibling_slot Hprefix) as Hslot.
   replace (0 + length prefix) with depth in Hslot by lia.
   exact Hslot. }
 apply Hslots. rewrite <- Hroute, <- Hsibling.
 rewrite Hhash, (Hcongruent key (fst entry) Hrelated). reflexivity.
Qed.

Lemma leaf_collision_disjoint :
 forall left_depth left_prefix left_hash (left_key : K) left_value
        right_depth right_prefix right_hash entries,
 left_hash <> right_hash ->
 wf left_depth left_prefix (Leaf left_hash left_key left_value) ->
 wf right_depth right_prefix (Collision right_hash entries) ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 forall entry, InA binding_equiv entry [(left_key, left_value)] ->
 InA binding_equiv entry entries -> False.
Proof.
 intros left_depth left_prefix left_hash left_key left_value right_depth
   right_prefix right_hash entries Hdifferent Hleft Hright Hcongruent entry
   Hinleft Hinright.
 destruct (inA_witness Hinleft) as [left_entry [Hinleft' Heleft]].
 simpl in Hinleft'. destruct Hinleft' as [Heq|[]]. subst left_entry.
 destruct (inA_witness Hinright) as [right_entry [Hinright' Heright]].
 assert (Hleft_hash : left_hash = hash seed left_key).
 { inversion Hleft; subst. reflexivity. }
 assert (Hright_hash : right_hash = hash seed (fst right_entry)).
 { now apply collision_binding_hash with (depth := right_depth) (prefix := right_prefix)
     (entries := entries). }
 apply Hdifferent. rewrite Hleft_hash, Hright_hash.
 rewrite <- (Hcongruent (fst entry) left_key Heleft).
 rewrite <- (Hcongruent (fst entry) (fst right_entry) Heright).
 reflexivity.
Qed.

Lemma collision_collision_disjoint :
 forall left_depth left_prefix left_hash left_entries
        right_depth right_prefix right_hash right_entries,
 left_hash <> right_hash ->
 wf left_depth left_prefix (Collision left_hash left_entries) ->
 wf right_depth right_prefix (Collision right_hash right_entries) ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 forall entry, InA binding_equiv entry left_entries ->
 InA binding_equiv entry right_entries -> False.
Proof.
 intros left_depth left_prefix left_hash left_entries right_depth right_prefix
   right_hash right_entries Hdifferent Hleft Hright Hcongruent entry Hinleft
   Hinright.
 destruct (inA_witness Hinleft) as [left_entry [Hinleft' Heleft]].
 destruct (inA_witness Hinright) as [right_entry [Hinright' Heright]].
 assert (Hleft_hash : left_hash = hash seed (fst left_entry)).
 { now apply collision_binding_hash with (depth := left_depth) (prefix := left_prefix)
     (entries := left_entries). }
 assert (Hright_hash : right_hash = hash seed (fst right_entry)).
 { now apply collision_binding_hash with (depth := right_depth) (prefix := right_prefix)
     (entries := right_entries). }
 apply Hdifferent. rewrite Hleft_hash, Hright_hash.
 rewrite <- (Hcongruent (fst entry) (fst left_entry) Heleft).
 rewrite <- (Hcongruent (fst entry) (fst right_entry) Heright).
 reflexivity.
Qed.

Lemma leaf_leaf_disjoint :
 forall left_depth left_prefix left_hash (left_key : K) left_value
        right_depth right_prefix right_hash (right_key : K) right_value,
 left_hash <> right_hash ->
 wf left_depth left_prefix (Leaf left_hash left_key left_value) ->
 wf right_depth right_prefix (Leaf right_hash right_key right_value) ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 forall entry, InA binding_equiv entry [(left_key, left_value)] ->
 InA binding_equiv entry [(right_key, right_value)] -> False.
Proof.
 intros left_depth left_prefix left_hash left_key left_value right_depth
   right_prefix right_hash right_key right_value Hdifferent Hleft Hright
   Hcongruent entry Hinleft Hinright.
 destruct (inA_witness Hinleft) as [left_entry [Hinleft' Heleft]].
 simpl in Hinleft'. destruct Hinleft' as [Heq|[]]. subst left_entry.
 destruct (inA_witness Hinright) as [right_entry [Hinright' Heright]].
 simpl in Hinright'. destruct Hinright' as [Heq|[]]. subst right_entry.
 assert (Hleft_hash : left_hash = hash seed left_key).
 { inversion Hleft; subst. reflexivity. }
 assert (Hright_hash : right_hash = hash seed right_key).
 { inversion Hright; subst. reflexivity. }
 apply Hdifferent. rewrite Hleft_hash, Hright_hash.
 rewrite <- (Hcongruent (fst entry) left_key Heleft).
 rewrite <- (Hcongruent (fst entry) right_key Heright).
 reflexivity.
Qed.

Lemma join_two_bindings_nodup :
 forall depth left_hash right_hash (left right : tree K A),
 Equivalence binding_equiv ->
 NoDupA binding_equiv (bindings left) ->
 NoDupA binding_equiv (bindings right) ->
 (forall entry, InA binding_equiv entry (bindings left) ->
   InA binding_equiv entry (bindings right) -> False) ->
 NoDupA binding_equiv (bindings (join_two left_hash left right_hash right depth)).
Proof.
 intros depth left_hash right_hash left right Hequiv Hleft Hright Hdisjoint.
 unfold join_two. destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth)).
 - simpl. rewrite app_nil_r. apply NoDupA_app; auto.
 - simpl. rewrite app_nil_r. apply NoDupA_app; auto.
   intros entry Hinright Hinleft. apply (Hdisjoint entry Hinleft Hinright).
Qed.

Lemma wf_join_two_disjoint :
 forall depth prefix left_hash right_hash (left right : tree K A),
 depth < branch_levels ->
 chunk left_hash depth <> chunk right_hash depth ->
 left <> Empty ->
 right <> Empty ->
 wf (S depth) (prefix ++ [chunk left_hash depth]) left ->
 wf (S depth) (prefix ++ [chunk right_hash depth]) right ->
 Equivalence binding_equiv ->
 (forall entry, InA binding_equiv entry (bindings left) ->
   InA binding_equiv entry (bindings right) -> False) ->
 wf depth prefix (join_two left_hash left right_hash right depth).
Proof.
  intros depth prefix left_hash right_hash left right Hdepth Hdifferent Hleftne Hrightne
    Hleft Hright Hequiv Hdisjoint.
  eapply wf_join_two; eauto.
  apply join_two_bindings_nodup; auto.
  - now apply wf_bindings_nodup with (depth := S depth)
      (prefix := prefix ++ [chunk left_hash depth]).
  - now apply wf_bindings_nodup with (depth := S depth)
      (prefix := prefix ++ [chunk right_hash depth]).
Qed.

Lemma wf_join_two_leaf_collision :
 forall depth prefix left_hash (left_key : K) left_value right_hash entries,
 depth < branch_levels ->
 left_hash <> right_hash ->
 chunk left_hash depth <> chunk right_hash depth ->
 wf (S depth) (prefix ++ [chunk left_hash depth])
   (Leaf left_hash left_key left_value) ->
 wf (S depth) (prefix ++ [chunk right_hash depth])
   (Collision right_hash entries) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf depth prefix
   (join_two left_hash (Leaf left_hash left_key left_value)
     right_hash (Collision right_hash entries) depth).
Proof.
 intros depth prefix left_hash left_key left_value right_hash entries Hdepth
   Hhashdifferent Hchunkdifferent Hleft Hright Hequiv Hcongruent.
 eapply wf_join_two_disjoint.
 - exact Hdepth.
 - exact Hchunkdifferent.
 - discriminate.
 - discriminate.
 - exact Hleft.
 - exact Hright.
 - apply binding_equiv_equiv. exact Hequiv.
 - apply (leaf_collision_disjoint
     (left_depth := S depth) (left_prefix := prefix ++ [chunk left_hash depth])
     (left_hash := left_hash) (left_key := left_key) (left_value := left_value)
     (right_depth := S depth) (right_prefix := prefix ++ [chunk right_hash depth])
     (right_hash := right_hash) (entries := entries)); auto.
Qed.

Lemma wf_join_two_collision_leaf :
 forall depth prefix left_hash left_entries right_hash (right_key : K) right_value,
 depth < branch_levels ->
 left_hash <> right_hash ->
 chunk left_hash depth <> chunk right_hash depth ->
 wf (S depth) (prefix ++ [chunk left_hash depth])
   (Collision left_hash left_entries) ->
 wf (S depth) (prefix ++ [chunk right_hash depth])
   (Leaf right_hash right_key right_value) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf depth prefix
   (join_two left_hash (Collision left_hash left_entries)
     right_hash (Leaf right_hash right_key right_value) depth).
Proof.
 intros depth prefix left_hash left_entries right_hash right_key right_value Hdepth
   Hhashdifferent Hchunkdifferent Hleft Hright Hequiv Hcongruent.
 eapply wf_join_two_disjoint.
 - exact Hdepth.
 - exact Hchunkdifferent.
 - discriminate.
 - discriminate.
 - exact Hleft.
 - exact Hright.
 - apply binding_equiv_equiv. exact Hequiv.
 - intros entry Hincollision Hinleaf.
   eapply (leaf_collision_disjoint
     (left_depth := S depth) (left_prefix := prefix ++ [chunk right_hash depth])
     (left_hash := right_hash) (left_key := right_key) (left_value := right_value)
     (right_depth := S depth) (right_prefix := prefix ++ [chunk left_hash depth])
     (right_hash := left_hash) (entries := left_entries)); eauto.
Qed.

Lemma wf_join_two_collision_collision :
 forall depth prefix left_hash left_entries right_hash right_entries,
 depth < branch_levels ->
 left_hash <> right_hash ->
 chunk left_hash depth <> chunk right_hash depth ->
 wf (S depth) (prefix ++ [chunk left_hash depth])
   (Collision left_hash left_entries) ->
 wf (S depth) (prefix ++ [chunk right_hash depth])
   (Collision right_hash right_entries) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf depth prefix
   (join_two left_hash (Collision left_hash left_entries)
     right_hash (Collision right_hash right_entries) depth).
Proof.
 intros depth prefix left_hash left_entries right_hash right_entries Hdepth
   Hhashdifferent Hchunkdifferent Hleft Hright Hequiv Hcongruent.
 eapply wf_join_two_disjoint.
 - exact Hdepth.
 - exact Hchunkdifferent.
 - discriminate.
 - discriminate.
 - exact Hleft.
 - exact Hright.
 - apply binding_equiv_equiv. exact Hequiv.
 - eapply (collision_collision_disjoint
     (left_depth := S depth) (left_prefix := prefix ++ [chunk left_hash depth])
     (left_hash := left_hash) (left_entries := left_entries)
     (right_depth := S depth) (right_prefix := prefix ++ [chunk right_hash depth])
     (right_hash := right_hash) (right_entries := right_entries)); eauto.
Qed.

Lemma wf_join_two_leaf_leaf :
 forall depth prefix left_hash (left_key : K) left_value
        right_hash (right_key : K) right_value,
 depth < branch_levels ->
 left_hash <> right_hash ->
 chunk left_hash depth <> chunk right_hash depth ->
 wf (S depth) (prefix ++ [chunk left_hash depth])
   (Leaf left_hash left_key left_value) ->
 wf (S depth) (prefix ++ [chunk right_hash depth])
   (Leaf right_hash right_key right_value) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf depth prefix
   (join_two left_hash (Leaf left_hash left_key left_value)
     right_hash (Leaf right_hash right_key right_value) depth).
Proof.
 intros depth prefix left_hash left_key left_value right_hash right_key right_value
   Hdepth Hhashdifferent Hchunkdifferent Hleft Hright Hequiv Hcongruent.
 eapply wf_join_two_disjoint.
 - exact Hdepth.
 - exact Hchunkdifferent.
 - discriminate.
 - discriminate.
 - exact Hleft.
 - exact Hright.
 - apply binding_equiv_equiv. exact Hequiv.
 - apply (leaf_leaf_disjoint
     (left_depth := S depth) (left_prefix := prefix ++ [chunk left_hash depth])
     (left_hash := left_hash) (left_key := left_key) (left_value := left_value)
     (right_depth := S depth) (right_prefix := prefix ++ [chunk right_hash depth])
     (right_hash := right_hash) (right_key := right_key)
     (right_value := right_value)); auto.
Qed.

Lemma wf_normalize_collision :
    forall depth prefix full_hash entries,
      Forall (entry_matches full_hash depth prefix) entries ->
      NoDupA binding_equiv entries ->
      wf depth prefix (normalize_collision full_hash entries).
  Proof.
    intros depth prefix full_hash entries Hentries Hnodup.
    destruct entries as [|[key value] [|[next_key next_value] tail]].
    - cbn [normalize_collision normalize_bucket]. constructor.
    - inversion Hentries as [|entry entries Hentry Htail]; subst.
      destruct Hentry as [Hhash [Hbound Hprefix]].
      cbn [normalize_collision normalize_bucket].
      eapply wf_leaf; eauto.
    - cbn [normalize_collision normalize_bucket].
      eapply wf_collision; eauto. simpl. lia.
  Qed.

Lemma wf_collision_remove :
    forall depth prefix full_hash entries (eqb : K -> K -> bool) key,
      wf depth prefix (Collision full_hash entries) ->
      wf depth prefix
        (normalize_collision full_hash (bucket_remove eqb key entries)).
  Proof.
    intros depth prefix full_hash entries eqb key Hwf.
    inversion Hwf as [| |depth' prefix' full_hash' entries' Hlength Hentries Hnodup|];
      subst.
    apply wf_normalize_collision.
    - now apply bucket_remove_forall.
    - now apply bucket_remove_nodup.
  Qed.

End WellFormed.

Section TableWellFormed.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.

  Definition table_wf (m : table K Seed A) : Prop :=
    wf E hash (table_seed m) 0 [] (table_root m).

  Lemma table_wf_empty :
    forall seed, table_wf (empty (K := K) (A := A) seed).
  Proof.
    intro seed. unfold table_wf, empty. apply wf_empty.
  Qed.

  Lemma table_wf_root :
    forall m, table_wf m ->
      wf E hash (table_seed m) 0 [] (table_root m).
  Proof. intros m Hwf. exact Hwf. Qed.

  Lemma table_wf_leaf :
    forall seed full_hash key (value : A),
      full_hash = hash seed key ->
      (full_hash < hash_space)%N ->
      table_wf {| table_seed := seed;
                  table_root := Leaf full_hash key value |}.
  Proof.
    intros seed full_hash key value Hhash Hbound.
    unfold table_wf. apply wf_leaf; [exact Hhash|exact Hbound|exact I].
  Qed.

  Lemma table_wf_set_empty :
    forall (eqb : K -> K -> bool) seed key (value : A),
      (hash seed key < hash_space)%N ->
      table_wf (set eqb hash key value (empty seed)).
  Proof.
    intros eqb seed key value Hbound.
    unfold set, empty, table_wf. cbn [set_tree].
    apply wf_leaf; [reflexivity|exact Hbound|exact I].
  Qed.

  Lemma table_wf_remove_empty :
    forall (eqb : K -> K -> bool) seed key,
      table_wf (remove eqb hash key (empty seed)).
  Proof.
    intros eqb seed key.
    unfold remove, empty, table_wf. cbn [remove_tree]. apply wf_empty.
  Qed.

  Lemma table_wf_singleton :
    forall (eqb : K -> K -> bool) seed key (value : A),
      (hash seed key < hash_space)%N ->
      table_wf (singleton eqb hash seed key value).
  Proof.
    intros eqb seed key value Hbound.
    unfold singleton. now apply table_wf_set_empty.
  Qed.

  Lemma table_wf_of_list_empty :
    forall (eqb : K -> K -> bool) seed,
      table_wf (of_list eqb hash seed []).
  Proof.
    intros eqb seed. unfold of_list. simpl. apply table_wf_empty.
  Qed.

  Lemma table_wf_of_list_singleton :
    forall (eqb : K -> K -> bool) seed key (value : A),
      (hash seed key < hash_space)%N ->
      table_wf (of_list eqb hash seed [(key, value)]).
  Proof.
    intros eqb seed key value Hbound.
    rewrite of_list_singleton. now apply table_wf_singleton.
  Qed.

  Lemma table_wf_of_list_first_wins_same_key :
    forall (eqb : K -> K -> bool) seed key (first second : A),
      (forall key, eqb key key = true) ->
      (hash seed key < hash_space)%N ->
      table_wf (of_list eqb hash seed [(key, first); (key, second)]).
  Proof.
    intros eqb seed key first second Heqb Hbound.
    rewrite of_list_first_wins_same_key by exact Heqb.
    now apply table_wf_singleton.
  Qed.

End TableWellFormed.

Lemma bindings_join_two :
  forall (K A : Type) depth left_hash right_hash (left right : tree K A)
         (entry : K * A),
    In entry (bindings (join_two left_hash left right_hash right depth)) <->
    In entry (bindings left) \/ In entry (bindings right).
Proof.
  intros K A depth left_hash right_hash left right entry.
  unfold join_two. destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth)).
  - simpl. rewrite app_nil_r. change (In entry (bindings left ++ bindings right) <->
      In entry (bindings left) \/ In entry (bindings right)).
    now rewrite in_app_iff.
  - simpl. rewrite app_nil_r. change (In entry (bindings right ++ bindings left) <->
      In entry (bindings left) \/ In entry (bindings right)).
    rewrite in_app_iff. tauto.
Qed.

Lemma bindings_join_worker :
  forall (K A : Type) fuel depth left_hash right_hash (left right : tree K A)
         (entry : K * A),
    In entry (bindings (join_worker fuel depth left_hash left right_hash right)) <->
    In entry (bindings left) \/ In entry (bindings right).
Proof.
  intros K A fuel. induction fuel as [|fuel IH];
    intros depth left_hash right_hash left right entry.
  - apply bindings_join_two.
  - cbn [join_worker]. destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)).
    + simpl. rewrite app_nil_r. apply IH.
    + apply bindings_join_two.
Qed.

(** This mirrors only the branch test in [join_worker].  It makes the fuel
    fallback observable in a small proposition without changing the source
    worker's extracted behavior. *)
Fixpoint join_falls_back (fuel depth : nat) (left_hash right_hash : N) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if N.eqb (chunk left_hash depth) (chunk right_hash depth)
      then join_falls_back fuel' (S depth) left_hash right_hash
      else false
  end.

Lemma join_worker_six_no_fallback :
  forall left_hash right_hash,
    (left_hash < hash_space)%N ->
    (right_hash < hash_space)%N ->
    left_hash <> right_hash ->
    join_falls_back branch_levels 0 left_hash right_hash = false.
Proof.
  intros left_hash right_hash Hleft Hright Hdifferent.
  cbn [join_falls_back branch_levels].
  destruct (N.eqb (chunk left_hash 0) (chunk right_hash 0)) eqn:H0; auto.
  destruct (N.eqb (chunk left_hash 1) (chunk right_hash 1)) eqn:H1; auto.
  destruct (N.eqb (chunk left_hash 2) (chunk right_hash 2)) eqn:H2; auto.
  destruct (N.eqb (chunk left_hash 3) (chunk right_hash 3)) eqn:H3; auto.
  destruct (N.eqb (chunk left_hash 4) (chunk right_hash 4)) eqn:H4; auto.
  destruct (N.eqb (chunk left_hash 5) (chunk right_hash 5)) eqn:H5; auto.
  exfalso. apply Hdifferent. eapply chunk_six_ext; eauto;
    apply N.eqb_eq; assumption.
Qed.

Lemma join_worker_suffix_no_fallback :
  forall depth left_hash right_hash,
    depth <= branch_levels ->
    (forall prior, prior < depth ->
      chunk left_hash prior = chunk right_hash prior) ->
    (left_hash < hash_space)%N ->
    (right_hash < hash_space)%N ->
    left_hash <> right_hash ->
    join_falls_back (branch_levels - depth) depth left_hash right_hash = false.
Proof.
  intros depth left_hash right_hash Hdepth Hprefix Hleft Hright Hdifferent.
  destruct depth as [|[|[|[|[|[|depth]]]]]].
  - exact (@join_worker_six_no_fallback left_hash right_hash Hleft Hright Hdifferent).
  - cbn [branch_levels join_falls_back] in Hdepth |-.
    change (join_falls_back 5 1 left_hash right_hash = false).
    cbn [join_falls_back].
    destruct (N.eqb (chunk left_hash 1) (chunk right_hash 1)) eqn:H1; auto.
    destruct (N.eqb (chunk left_hash 2) (chunk right_hash 2)) eqn:H2; auto.
    destruct (N.eqb (chunk left_hash 3) (chunk right_hash 3)) eqn:H3; auto.
    destruct (N.eqb (chunk left_hash 4) (chunk right_hash 4)) eqn:H4; auto.
    destruct (N.eqb (chunk left_hash 5) (chunk right_hash 5)) eqn:H5; auto.
    assert (H0 : chunk left_hash 0 = chunk right_hash 0) by (apply Hprefix; lia).
    assert (H1' : chunk left_hash 1 = chunk right_hash 1) by now apply N.eqb_eq.
    assert (H2' : chunk left_hash 2 = chunk right_hash 2) by now apply N.eqb_eq.
    assert (H3' : chunk left_hash 3 = chunk right_hash 3) by now apply N.eqb_eq.
    assert (H4' : chunk left_hash 4 = chunk right_hash 4) by now apply N.eqb_eq.
    assert (H5' : chunk left_hash 5 = chunk right_hash 5) by now apply N.eqb_eq.
    exfalso. apply Hdifferent. eapply chunk_six_ext; eauto.
  - cbn [branch_levels join_falls_back] in Hdepth |-.
    change (join_falls_back 4 2 left_hash right_hash = false).
    cbn [join_falls_back].
    destruct (N.eqb (chunk left_hash 2) (chunk right_hash 2)) eqn:H2; auto.
    destruct (N.eqb (chunk left_hash 3) (chunk right_hash 3)) eqn:H3; auto.
    destruct (N.eqb (chunk left_hash 4) (chunk right_hash 4)) eqn:H4; auto.
    destruct (N.eqb (chunk left_hash 5) (chunk right_hash 5)) eqn:H5; auto.
    assert (H0 : chunk left_hash 0 = chunk right_hash 0) by (apply Hprefix; lia).
    assert (H1' : chunk left_hash 1 = chunk right_hash 1) by (apply Hprefix; lia).
    assert (H2' : chunk left_hash 2 = chunk right_hash 2) by now apply N.eqb_eq.
    assert (H3' : chunk left_hash 3 = chunk right_hash 3) by now apply N.eqb_eq.
    assert (H4' : chunk left_hash 4 = chunk right_hash 4) by now apply N.eqb_eq.
    assert (H5' : chunk left_hash 5 = chunk right_hash 5) by now apply N.eqb_eq.
    exfalso. apply Hdifferent. eapply chunk_six_ext; eauto.
  - cbn [branch_levels join_falls_back] in Hdepth |-.
    change (join_falls_back 3 3 left_hash right_hash = false).
    cbn [join_falls_back].
    destruct (N.eqb (chunk left_hash 3) (chunk right_hash 3)) eqn:H3; auto.
    destruct (N.eqb (chunk left_hash 4) (chunk right_hash 4)) eqn:H4; auto.
    destruct (N.eqb (chunk left_hash 5) (chunk right_hash 5)) eqn:H5; auto.
    assert (H0 : chunk left_hash 0 = chunk right_hash 0) by (apply Hprefix; lia).
    assert (H1' : chunk left_hash 1 = chunk right_hash 1) by (apply Hprefix; lia).
    assert (H2' : chunk left_hash 2 = chunk right_hash 2) by (apply Hprefix; lia).
    assert (H3' : chunk left_hash 3 = chunk right_hash 3) by now apply N.eqb_eq.
    assert (H4' : chunk left_hash 4 = chunk right_hash 4) by now apply N.eqb_eq.
    assert (H5' : chunk left_hash 5 = chunk right_hash 5) by now apply N.eqb_eq.
    exfalso. apply Hdifferent. eapply chunk_six_ext; eauto.
  - cbn [branch_levels join_falls_back] in Hdepth |-.
    change (join_falls_back 2 4 left_hash right_hash = false).
    cbn [join_falls_back].
    destruct (N.eqb (chunk left_hash 4) (chunk right_hash 4)) eqn:H4; auto.
    destruct (N.eqb (chunk left_hash 5) (chunk right_hash 5)) eqn:H5; auto.
    assert (H0 : chunk left_hash 0 = chunk right_hash 0) by (apply Hprefix; lia).
    assert (H1' : chunk left_hash 1 = chunk right_hash 1) by (apply Hprefix; lia).
    assert (H2' : chunk left_hash 2 = chunk right_hash 2) by (apply Hprefix; lia).
    assert (H3' : chunk left_hash 3 = chunk right_hash 3) by (apply Hprefix; lia).
    assert (H4' : chunk left_hash 4 = chunk right_hash 4) by now apply N.eqb_eq.
    assert (H5' : chunk left_hash 5 = chunk right_hash 5) by now apply N.eqb_eq.
    exfalso. apply Hdifferent. eapply chunk_six_ext; eauto.
  - cbn [branch_levels join_falls_back] in Hdepth |-.
    change (join_falls_back 1 5 left_hash right_hash = false).
    cbn [join_falls_back].
    destruct (N.eqb (chunk left_hash 5) (chunk right_hash 5)) eqn:H5; auto.
    assert (H0 : chunk left_hash 0 = chunk right_hash 0) by (apply Hprefix; lia).
    assert (H1' : chunk left_hash 1 = chunk right_hash 1) by (apply Hprefix; lia).
    assert (H2' : chunk left_hash 2 = chunk right_hash 2) by (apply Hprefix; lia).
    assert (H3' : chunk left_hash 3 = chunk right_hash 3) by (apply Hprefix; lia).
    assert (H4' : chunk left_hash 4 = chunk right_hash 4) by (apply Hprefix; lia).
    assert (H5' : chunk left_hash 5 = chunk right_hash 5) by now apply N.eqb_eq.
    exfalso. apply Hdifferent. eapply chunk_six_ext; eauto.
  - cbn [branch_levels join_falls_back] in Hdepth |-.
    change (join_falls_back 0 6 left_hash right_hash = false).
    cbn [join_falls_back].
    assert (H0 : chunk left_hash 0 = chunk right_hash 0) by (apply Hprefix; lia).
    assert (H1' : chunk left_hash 1 = chunk right_hash 1) by (apply Hprefix; lia).
    assert (H2' : chunk left_hash 2 = chunk right_hash 2) by (apply Hprefix; lia).
    assert (H3' : chunk left_hash 3 = chunk right_hash 3) by (apply Hprefix; lia).
    assert (H4' : chunk left_hash 4 = chunk right_hash 4) by (apply Hprefix; lia).
    assert (H5' : chunk left_hash 5 = chunk right_hash 5) by (apply Hprefix; lia).
    exfalso. apply Hdifferent. eapply chunk_six_ext; eauto.
Qed.

Section RecursiveLeafJoin.

Context {K Seed A : Type}.
Variable E : K -> K -> Prop.
Variable hash : Seed -> K -> N.
Variable seed : Seed.

Lemma wf_join_worker_leaf_leaf :
 forall fuel depth prefix left_hash (left_key : K) (left_value : A)
        right_hash (right_key : K) (right_value : A),
 depth + fuel <= branch_levels ->
 length prefix = depth ->
 left_hash <> right_hash ->
 wf E hash seed depth prefix (Leaf left_hash left_key left_value) ->
 wf E hash seed depth prefix (Leaf right_hash right_key right_value) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 join_falls_back fuel depth left_hash right_hash = false ->
 wf E hash seed depth prefix
   (join_worker fuel depth left_hash (Leaf left_hash left_key left_value)
    right_hash (Leaf right_hash right_key right_value)).
Proof.
 induction fuel as [|fuel IH]; intros depth prefix left_hash left_key left_value
   right_hash right_key right_value Hfuel Hlength Hdifferent Hleft Hright
   Hequiv Hcongruent Hfallback.
 - simpl in Hfallback. discriminate.
 - cbn [join_worker join_falls_back] in Hfallback |-.
   destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hequal.
   + apply wf_join_worker_equal_wf.
     * lia.
     * exact Hequal.
     * apply IH with (left_key := left_key) (left_value := left_value)
         (right_key := right_key) (right_value := right_value).
       -- lia.
       -- simpl. rewrite app_length. simpl. lia.
       -- exact Hdifferent.
       -- apply (wf_leaf_descend (full_hash := left_hash)
            (key := left_key) (value := left_value)); auto.
       -- apply N.eqb_eq in Hequal. rewrite Hequal.
          apply (wf_leaf_descend (full_hash := right_hash)
            (key := right_key) (value := right_value)); auto.
       -- exact Hequiv.
       -- exact Hcongruent.
       -- exact Hfallback.
   + apply N.eqb_neq in Hequal.
     cbn [join_worker].
     assert (Hdifferentb : N.eqb (chunk left_hash depth)
       (chunk right_hash depth) = false) by (apply N.eqb_neq; exact Hequal).
     rewrite Hdifferentb.
     apply wf_join_two_leaf_leaf.
     * lia.
     * exact Hdifferent.
     * exact Hequal.
     * apply (wf_leaf_descend (full_hash := left_hash)
          (key := left_key) (value := left_value)); auto.
     * apply (wf_leaf_descend (full_hash := right_hash)
          (key := right_key) (value := right_value)); auto.
     * exact Hequiv.
     * exact Hcongruent.
Qed.

Lemma wf_join_worker_leaf_leaf_root :
 forall left_hash (left_key : K) (left_value : A)
        right_hash (right_key : K) (right_value : A),
 left_hash <> right_hash ->
 wf E hash seed 0 [] (Leaf left_hash left_key left_value) ->
 wf E hash seed 0 [] (Leaf right_hash right_key right_value) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf E hash seed 0 []
   (join_worker branch_levels 0 left_hash (Leaf left_hash left_key left_value)
    right_hash (Leaf right_hash right_key right_value)).
Proof.
 intros left_hash left_key left_value right_hash right_key right_value
   Hdifferent Hleft Hright Hequiv Hcongruent.
 assert (Hleft_bound : (left_hash < hash_space)%N).
 { inversion Hleft; subst. assumption. }
 assert (Hright_bound : (right_hash < hash_space)%N).
 { inversion Hright; subst. assumption. }
 apply wf_join_worker_leaf_leaf.
 - cbv [branch_levels]. lia.
 - reflexivity.
 - exact Hdifferent.
 - exact Hleft.
 - exact Hright.
 - exact Hequiv.
 - exact Hcongruent.
 - apply join_worker_six_no_fallback; assumption.
Qed.

Lemma wf_join_worker_leaf_collision :
 forall fuel depth prefix left_hash (left_key : K) (left_value : A)
        right_hash (right_entries : list (K * A)),
 depth + fuel <= branch_levels ->
 length prefix = depth ->
 left_hash <> right_hash ->
 wf E hash seed depth prefix (Leaf left_hash left_key left_value) ->
 wf E hash seed depth prefix (Collision right_hash right_entries) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 join_falls_back fuel depth left_hash right_hash = false ->
 wf E hash seed depth prefix
   (join_worker fuel depth left_hash (Leaf left_hash left_key left_value)
    right_hash (Collision right_hash right_entries)).
Proof.
 induction fuel as [|fuel IH]; intros depth prefix left_hash left_key left_value
   right_hash right_entries Hfuel Hlength Hdifferent Hleft Hright Hequiv
   Hcongruent Hfallback.
 - simpl in Hfallback. discriminate.
 - cbn [join_worker join_falls_back] in Hfallback |-.
   destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hequal.
   + apply wf_join_worker_equal_wf.
     * lia.
     * exact Hequal.
     * apply IH with (left_key := left_key) (left_value := left_value).
       -- lia.
       -- simpl. rewrite app_length. simpl. lia.
       -- exact Hdifferent.
       -- apply (wf_leaf_descend (full_hash := left_hash)
            (key := left_key) (value := left_value)); auto.
       -- apply N.eqb_eq in Hequal. rewrite Hequal.
          apply (wf_collision_descend (full_hash := right_hash)
            (entries := right_entries)); auto.
       -- exact Hequiv.
       -- exact Hcongruent.
       -- exact Hfallback.
   + apply N.eqb_neq in Hequal.
     cbn [join_worker].
     assert (Hdifferentb : N.eqb (chunk left_hash depth)
       (chunk right_hash depth) = false) by (apply N.eqb_neq; exact Hequal).
     rewrite Hdifferentb.
     apply wf_join_two_leaf_collision.
     * lia.
     * exact Hdifferent.
     * exact Hequal.
     * apply (wf_leaf_descend (full_hash := left_hash)
          (key := left_key) (value := left_value)); auto.
     * apply (wf_collision_descend (full_hash := right_hash)
          (entries := right_entries)); auto.
     * exact Hequiv.
     * exact Hcongruent.
Qed.

Lemma wf_join_worker_leaf_collision_root :
 forall left_hash (left_key : K) (left_value : A)
        right_hash (right_entries : list (K * A)),
 left_hash <> right_hash ->
 wf E hash seed 0 [] (Leaf left_hash left_key left_value) ->
 wf E hash seed 0 [] (Collision right_hash right_entries) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf E hash seed 0 []
   (join_worker branch_levels 0 left_hash (Leaf left_hash left_key left_value)
    right_hash (Collision right_hash right_entries)).
Proof.
 intros left_hash left_key left_value right_hash right_entries Hdifferent Hleft
   Hright Hequiv Hcongruent.
 assert (Hleft_bound : (left_hash < hash_space)%N).
 { inversion Hleft; subst. assumption. }
 assert (Hright_bound : (right_hash < hash_space)%N).
 { eapply wf_collision_hash_bound; exact Hright. }
 apply wf_join_worker_leaf_collision.
 - cbv [branch_levels]. lia.
 - reflexivity.
 - exact Hdifferent.
 - exact Hleft.
 - exact Hright.
 - exact Hequiv.
 - exact Hcongruent.
 - apply join_worker_six_no_fallback; assumption.
Qed.

Lemma wf_join_worker_collision_leaf :
 forall fuel depth prefix left_hash (left_entries : list (K * A))
        right_hash (right_key : K) (right_value : A),
 depth + fuel <= branch_levels ->
 length prefix = depth ->
 left_hash <> right_hash ->
 wf E hash seed depth prefix (Collision left_hash left_entries) ->
 wf E hash seed depth prefix (Leaf right_hash right_key right_value) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 join_falls_back fuel depth left_hash right_hash = false ->
 wf E hash seed depth prefix
   (join_worker fuel depth left_hash (Collision left_hash left_entries)
    right_hash (Leaf right_hash right_key right_value)).
Proof.
 induction fuel as [|fuel IH]; intros depth prefix left_hash left_entries
   right_hash right_key right_value Hfuel Hlength Hdifferent Hleft Hright
   Hequiv Hcongruent Hfallback.
 - simpl in Hfallback. discriminate.
 - cbn [join_worker join_falls_back] in Hfallback |-.
   destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hequal.
   + apply wf_join_worker_equal_wf.
     * lia.
     * exact Hequal.
     * apply IH with (right_key := right_key) (right_value := right_value).
       -- lia.
       -- simpl. rewrite app_length. simpl. lia.
       -- exact Hdifferent.
       -- apply (wf_collision_descend (full_hash := left_hash)
            (entries := left_entries)); auto.
       -- apply N.eqb_eq in Hequal. rewrite Hequal.
          apply (wf_leaf_descend (full_hash := right_hash)
            (key := right_key) (value := right_value)); auto.
       -- exact Hequiv.
       -- exact Hcongruent.
       -- exact Hfallback.
   + apply N.eqb_neq in Hequal.
     cbn [join_worker].
     assert (Hdifferentb : N.eqb (chunk left_hash depth)
       (chunk right_hash depth) = false) by (apply N.eqb_neq; exact Hequal).
     rewrite Hdifferentb.
     apply wf_join_two_collision_leaf.
     * lia.
     * exact Hdifferent.
     * exact Hequal.
     * apply (wf_collision_descend (full_hash := left_hash)
          (entries := left_entries)); auto.
     * apply (wf_leaf_descend (full_hash := right_hash)
          (key := right_key) (value := right_value)); auto.
     * exact Hequiv.
     * exact Hcongruent.
Qed.

Lemma wf_join_worker_collision_leaf_root :
 forall left_hash (left_entries : list (K * A))
        right_hash (right_key : K) (right_value : A),
 left_hash <> right_hash ->
 wf E hash seed 0 [] (Collision left_hash left_entries) ->
 wf E hash seed 0 [] (Leaf right_hash right_key right_value) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf E hash seed 0 []
   (join_worker branch_levels 0 left_hash (Collision left_hash left_entries)
    right_hash (Leaf right_hash right_key right_value)).
Proof.
 intros left_hash left_entries right_hash right_key right_value Hdifferent Hleft
   Hright Hequiv Hcongruent.
 assert (Hleft_bound : (left_hash < hash_space)%N).
 { eapply wf_collision_hash_bound; exact Hleft. }
 assert (Hright_bound : (right_hash < hash_space)%N).
 { inversion Hright; subst. assumption. }
 apply wf_join_worker_collision_leaf.
 - cbv [branch_levels]. lia.
 - reflexivity.
 - exact Hdifferent.
 - exact Hleft.
 - exact Hright.
 - exact Hequiv.
 - exact Hcongruent.
 - apply join_worker_six_no_fallback; assumption.
Qed.

Lemma wf_join_worker_collision_collision :
 forall fuel depth prefix left_hash (left_entries : list (K * A))
        right_hash (right_entries : list (K * A)),
 depth + fuel <= branch_levels ->
 length prefix = depth ->
 left_hash <> right_hash ->
 wf E hash seed depth prefix (Collision left_hash left_entries) ->
 wf E hash seed depth prefix (Collision right_hash right_entries) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 join_falls_back fuel depth left_hash right_hash = false ->
 wf E hash seed depth prefix
   (join_worker fuel depth left_hash (Collision left_hash left_entries)
    right_hash (Collision right_hash right_entries)).
Proof.
 induction fuel as [|fuel IH]; intros depth prefix left_hash left_entries
   right_hash right_entries Hfuel Hlength Hdifferent Hleft Hright Hequiv
   Hcongruent Hfallback.
 - simpl in Hfallback. discriminate.
 - cbn [join_worker join_falls_back] in Hfallback |-.
   destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hequal.
   + apply wf_join_worker_equal_wf.
     * lia.
     * exact Hequal.
     * apply IH.
       -- lia.
       -- simpl. rewrite app_length. simpl. lia.
       -- exact Hdifferent.
       -- apply (wf_collision_descend (full_hash := left_hash)
            (entries := left_entries)); auto.
       -- apply N.eqb_eq in Hequal. rewrite Hequal.
          apply (wf_collision_descend (full_hash := right_hash)
            (entries := right_entries)); auto.
       -- exact Hequiv.
       -- exact Hcongruent.
       -- exact Hfallback.
   + apply N.eqb_neq in Hequal.
     cbn [join_worker].
     assert (Hdifferentb : N.eqb (chunk left_hash depth)
       (chunk right_hash depth) = false) by (apply N.eqb_neq; exact Hequal).
     rewrite Hdifferentb.
     apply wf_join_two_collision_collision.
     * lia.
     * exact Hdifferent.
     * exact Hequal.
     * apply (wf_collision_descend (full_hash := left_hash)
          (entries := left_entries)); auto.
     * apply (wf_collision_descend (full_hash := right_hash)
          (entries := right_entries)); auto.
     * exact Hequiv.
     * exact Hcongruent.
Qed.

Lemma wf_join_worker_collision_collision_root :
 forall left_hash (left_entries : list (K * A))
        right_hash (right_entries : list (K * A)),
 left_hash <> right_hash ->
 wf E hash seed 0 [] (Collision left_hash left_entries) ->
 wf E hash seed 0 [] (Collision right_hash right_entries) ->
 Equivalence E ->
 (forall first second, E first second -> hash seed first = hash seed second) ->
 wf E hash seed 0 []
   (join_worker branch_levels 0 left_hash (Collision left_hash left_entries)
    right_hash (Collision right_hash right_entries)).
Proof.
 intros left_hash left_entries right_hash right_entries Hdifferent Hleft Hright
   Hequiv Hcongruent.
 assert (Hleft_bound : (left_hash < hash_space)%N).
 { eapply wf_collision_hash_bound; exact Hleft. }
 assert (Hright_bound : (right_hash < hash_space)%N).
 { eapply wf_collision_hash_bound; exact Hright. }
 apply wf_join_worker_collision_collision.
 - cbv [branch_levels]. lia.
 - reflexivity.
 - exact Hdifferent.
 - exact Hleft.
 - exact Hright.
 - exact Hequiv.
 - exact Hcongruent.
 - apply join_worker_six_no_fallback; assumption.
Qed.


End RecursiveLeafJoin.

Lemma get_tree_zero_branch :
  forall (K A : Type) (eqb : K -> K -> bool) depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    get_tree eqb 0 depth full_hash key (Branch bitmap children) = None.
Proof. reflexivity. Qed.

Lemma get_set_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         seed query key (value : A),
    hash seed query = hash seed key ->
    get eqb hash query (set eqb hash key value (empty seed)) =
    if eqb query key then Some value else None.
Proof.
  intros K Seed A eqb hash seed query key value Hhash.
  unfold get, set, empty. cbn [set_tree get_tree].
  change (get_tree eqb branch_levels 0 (hash seed query) query
    (Leaf (hash seed key) key value) =
    (if eqb query key then Some value else None)).
  rewrite Hhash. cbv [branch_levels]. cbn [get_tree].
  now rewrite N.eqb_refl.
Qed.

Lemma get_singleton_query :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         seed query stored (value : A),
    hash seed query = hash seed stored ->
    get eqb hash query (singleton eqb hash seed stored value) =
    if eqb query stored then Some value else None.
Proof.
  intros K Seed A eqb hash seed query stored value Hhash.
  unfold singleton. now apply get_set_empty.
Qed.

Lemma mem_singleton_query :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         seed query stored (value : A),
    hash seed query = hash seed stored ->
    mem eqb hash query (singleton eqb hash seed stored value) =
    if eqb query stored then true else false.
Proof.
  intros K Seed A eqb hash seed query stored value Hhash.
  unfold mem. rewrite (@get_singleton_query K Seed A eqb hash seed query
    stored value Hhash).
  destruct (eqb query stored); reflexivity.
Qed.

Lemma get_set_singleton_replace :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         seed key stored (old_value value : A),
    hash seed key = hash seed stored ->
    eqb key stored = true ->
    get eqb hash key
      (set eqb hash key value (singleton eqb hash seed stored old_value)) =
    Some value.
Proof.
  intros K Seed A eqb hash seed key stored old_value value Hhash Hmatch.
  unfold get, set, singleton, empty. cbn [set_tree get_tree].
  cbn.
  rewrite Hmatch. cbn [get_tree].
  now rewrite Hhash, N.eqb_refl, Hmatch.
Qed.

Lemma get_remove_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         seed query key,
    get eqb hash query (remove eqb hash key (empty (A := A) seed)) = None.
Proof.
  intros K Seed A eqb hash seed query key.
  unfold get, remove, empty. cbn [remove_tree].
  cbv [branch_levels]. reflexivity.
Qed.

Lemma get_of_list_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         seed query,
    get eqb hash query (@of_list K Seed A eqb hash seed []) = None.
Proof.
  intros K Seed A eqb hash seed query.
  unfold of_list. simpl. apply get_empty.
Qed.

Lemma set_tree_zero_branch :
  forall (K A : Type) (eqb : K -> K -> bool) depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)),
    set_tree eqb 0 depth full_hash key value (Branch bitmap children) =
    Branch bitmap children.
Proof. reflexivity. Qed.

Lemma remove_tree_zero_branch :
  forall (K A : Type) (eqb : K -> K -> bool) depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    remove_tree eqb 0 depth full_hash key (Branch bitmap children) =
    Branch bitmap children.
Proof. reflexivity. Qed.

Lemma get_tree_branch_slot_absent :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    bitmap_has bitmap (chunk full_hash depth) = false ->
    get_tree eqb (S fuel) depth full_hash key (Branch bitmap children) = None.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children Habsent.
  cbn [get_tree]. now rewrite Habsent.
Qed.

Lemma get_tree_branch_child :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)) (child : tree K A),
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    get_tree eqb (S fuel) depth full_hash key (Branch bitmap children) =
    get_tree eqb fuel (S depth) full_hash key child.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children child Hpresent Hchild.
  cbn [get_tree]. now rewrite Hpresent, Hchild.
Qed.

Lemma get_tree_branch_wf_child :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    exists child,
      get_tree eqb (S fuel) depth full_hash key (Branch bitmap children) =
      get_tree eqb fuel (S depth) full_hash key child /\
      child <> Empty /\ wf E hash seed (S depth)
        (prefix ++ [chunk full_hash depth]) child.
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children eqb
    Hwf Hpresent.
  destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hpresent)
    as [child [Hchild [Hnonempty Hchildwf]]].
  exists child. split.
  - now apply get_tree_branch_child.
  - split; assumption.
Qed.

Lemma get_tree_branch_dense_missing :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = None ->
    get_tree eqb (S fuel) depth full_hash key (Branch bitmap children) = None.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children Hpresent Hmissing.
  cbn [get_tree]. now rewrite Hpresent, Hmissing.
Qed.

Lemma set_tree_branch_slot_absent :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)),
    bitmap_has bitmap (chunk full_hash depth) = false ->
    set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children) =
    branch_insert bitmap (chunk full_hash depth) (Leaf full_hash key value) children.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap children Habsent.
  cbn [set_tree]. now rewrite Habsent.
Qed.

Lemma set_tree_branch_slot_absent_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K) (value : A)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = false ->
    wf E hash seed (S depth) (prefix ++ [chunk full_hash depth])
      (Leaf full_hash key value) ->
    NoDupA (binding_equiv E)
      (bindings (branch_insert bitmap (chunk full_hash depth)
        (Leaf full_hash key value) children)) ->
    wf E hash seed depth prefix
      (set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key value bitmap
    children eqb Hwf Habsent Hleaf Hnodup.
  rewrite set_tree_branch_slot_absent by exact Habsent.
  apply wf_branch_insert_absent; try assumption.
  - apply chunk_bound.
  - discriminate.
Qed.

Lemma set_tree_branch_slot_absent_wf_leaf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K) (value : A)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = false ->
    length prefix = depth ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    NoDupA (binding_equiv E)
      (bindings (branch_insert bitmap (chunk full_hash depth)
        (Leaf full_hash key value) children)) ->
    wf E hash seed depth prefix
      (set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key value bitmap
    children eqb Hwf Habsent Hprefix_len Hhash Hhash_bound Hprefix Hnodup.
  apply set_tree_branch_slot_absent_wf with
    (full_hash := full_hash) (key := key) (value := value);
    try assumption.
  apply wf_leaf; try assumption.
  now apply prefix_matches_append_slot.
Qed.

Lemma set_tree_branch_child :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)) (child : tree K A),
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children) =
    branch_replace bitmap (chunk full_hash depth)
      (set_tree eqb fuel (S depth) full_hash key value child) children.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap children child Hpresent Hchild.
  cbn [set_tree]. now rewrite Hpresent, Hchild.
Qed.

Lemma set_tree_branch_wf_child :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K) (value : A)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    exists child,
      set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children) =
      branch_replace bitmap (chunk full_hash depth)
        (set_tree eqb fuel (S depth) full_hash key value child) children /\
      child <> Empty /\ wf E hash seed (S depth)
        (prefix ++ [chunk full_hash depth]) child.
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key value bitmap
    children eqb Hwf Hpresent.
  destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hpresent)
    as [child [Hchild [Hnonempty Hchildwf]]].
  exists child. split.
  - now apply set_tree_branch_child.
  - split; assumption.
Qed.

Lemma set_tree_branch_child_wf_nonempty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K) (value : A)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool)
         child child',
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    set_tree eqb fuel (S depth) full_hash key value child = child' ->
    child' <> Empty ->
    wf E hash seed (S depth) (prefix ++ [chunk full_hash depth]) child' ->
    NoDupA (binding_equiv E)
      (bindings (branch_replace bitmap (chunk full_hash depth) child' children)) ->
    wf E hash seed depth prefix
      (set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key value bitmap
    children eqb child child' Hwf Hpresent Hchild Hset Hnonempty Hchildwf Hnodup.
  rewrite (set_tree_branch_child eqb fuel depth full_hash key value bitmap
    children Hpresent Hchild).
  rewrite Hset.
  apply wf_branch_replace; assumption || apply chunk_bound.
Qed.

Lemma set_tree_branch_dense_missing :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)),
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = None ->
    set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children) =
    branch_insert bitmap (chunk full_hash depth) (Leaf full_hash key value) children.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap children Hpresent Hmissing.
  cbn [set_tree]. now rewrite Hpresent, Hmissing.
Qed.

Lemma remove_tree_branch_slot_absent :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    bitmap_has bitmap (chunk full_hash depth) = false ->
    remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children) =
    Branch bitmap children.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children Habsent.
  cbn [remove_tree]. now rewrite Habsent.
Qed.

Lemma remove_tree_branch_slot_absent_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = false ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children eqb
    Hwf Habsent.
  rewrite remove_tree_branch_slot_absent by exact Habsent.
  exact Hwf.
Qed.

Lemma remove_tree_branch_child :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)) (child : tree K A),
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children) =
    match remove_tree eqb fuel (S depth) full_hash key child with
    | Empty => branch_remove bitmap (chunk full_hash depth) children
    | Leaf child_hash child_key child_value =>
        branch_replace bitmap (chunk full_hash depth)
          (Leaf child_hash child_key child_value) children
    | Collision child_hash child_entries =>
        branch_replace bitmap (chunk full_hash depth)
          (Collision child_hash child_entries) children
    | Branch child_bitmap child_children =>
        branch_replace bitmap (chunk full_hash depth)
          (Branch child_bitmap child_children) children
    end.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children child Hpresent Hchild.
  cbn [remove_tree]. rewrite Hpresent, Hchild.
  destruct (remove_tree eqb fuel (S depth) full_hash key child); reflexivity.
Qed.

Lemma remove_tree_branch_wf_child :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    exists child,
      remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children) =
      match remove_tree eqb fuel (S depth) full_hash key child with
      | Empty => branch_remove bitmap (chunk full_hash depth) children
      | Leaf child_hash child_key child_value =>
          branch_replace bitmap (chunk full_hash depth)
            (Leaf child_hash child_key child_value) children
      | Collision child_hash child_entries =>
          branch_replace bitmap (chunk full_hash depth)
            (Collision child_hash child_entries) children
      | Branch child_bitmap child_children =>
          branch_replace bitmap (chunk full_hash depth)
            (Branch child_bitmap child_children) children
      end /\
      child <> Empty /\ wf E hash seed (S depth)
        (prefix ++ [chunk full_hash depth]) child.
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children eqb
    Hwf Hpresent.
  destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hpresent)
    as [child [Hchild [Hnonempty Hchildwf]]].
  exists child. split.
  - now apply remove_tree_branch_child.
  - split; assumption.
Qed.

Lemma remove_tree_branch_child_wf_nonempty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool)
         child child',
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    remove_tree eqb fuel (S depth) full_hash key child = child' ->
    child' <> Empty ->
    wf E hash seed (S depth) (prefix ++ [chunk full_hash depth]) child' ->
    NoDupA (binding_equiv E)
      (bindings (branch_replace bitmap (chunk full_hash depth) child' children)) ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children eqb
    child child' Hwf Hpresent Hchild Hremove Hnonempty Hchildwf Hnodup.
  rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
    children Hpresent Hchild).
  rewrite Hremove.
  destruct child'; try contradiction.
  all: apply wf_branch_replace; assumption || apply chunk_bound.
Qed.

Lemma branch_remove_wf_singleton_empty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) depth prefix bitmap (children : list (tree K A)) slot,
    wf E hash seed depth prefix (Branch bitmap children) ->
    length children = 1 ->
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    branch_remove bitmap slot children = Empty.
Proof.
  intros K Seed A E hash seed depth prefix bitmap children slot Hwf Hlength
    Hslot Hpresent.
  destruct (wf_branch_ranked_child Hwf Hslot Hpresent)
    as [child [Hget [Hnonempty Hchild]]].
  assert (Hindex : rank bitmap slot < length children).
  { apply (proj1 (nth_error_Some children (rank bitmap slot))).
    unfold dense_get in Hget. rewrite Hget. discriminate. }
  assert (Hremoved_length : length (dense_remove (rank bitmap slot) children) = 0).
  { rewrite dense_remove_length_hit by exact Hindex.
    rewrite Hlength. reflexivity. }
  apply length_zero_iff_nil in Hremoved_length.
  unfold branch_remove. now rewrite Hremoved_length.
Qed.

Lemma wf_branch_remove_present_nonempty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (depth : nat) (prefix : list N) (bitmap : N)
         (children : list (tree K A)) (slot : N),
    wf E hash seed depth prefix (Branch bitmap children) ->
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    dense_remove (rank bitmap slot) children <> [] ->
    NoDupA (binding_equiv E)
      (bindings (Branch (N.ldiff bitmap (bitmap_bit slot))
        (dense_remove (rank bitmap slot) children))) ->
    wf E hash seed depth prefix
      (Branch (N.ldiff bitmap (bitmap_bit slot))
        (dense_remove (rank bitmap slot) children)).
Proof.
  intros K Seed A E hash seed depth prefix bitmap children slot Hwf Hslot
    Hpresent Hremaining Hnodup.
  inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren
    Holdnodup]; subst.
  destruct (@occupied_slots_ldiff_bit_present_split bitmap slot Hslot Hpresent)
    as [before [after [Hslots [Hrank Hnew]]]].
  rewrite Hslots in Hchildren.
  destruct (@Forall2_app_inv_l N (tree K A)
    (fun routed inserted => inserted <> Empty /\
      wf E hash seed (S depth) (prefix ++ [routed]) inserted)
    before (slot :: after) children Hchildren)
    as [children_before [remaining
      [Hbefore [Hrest Hchildren_eq]]]].
  inversion Hrest as [|routed removed_child after_slots children_after
    Hremoved Hafter]; subst routed remaining.
  assert (Hbefore_length : length children_before = length before).
  { symmetry. exact (@Forall2_length N (tree K A)
      (fun routed inserted => inserted <> Empty /\
        wf E hash seed (S depth) (prefix ++ [routed]) inserted)
      before children_before Hbefore). }
  assert (Hdense : dense_remove (rank bitmap slot) children =
    children_before ++ children_after).
  { rewrite Hchildren_eq, <- Hrank, <- Hbefore_length.
    apply dense_remove_at_append. }
  assert (Hdense_nonempty : children_before ++ children_after <> []).
  { intro Hempty. apply Hremaining. now rewrite Hdense, Hempty. }
  unfold branch_remove in Hnodup.
  destruct (dense_remove (rank bitmap slot) children) as [|head tail] eqn:Hremove;
    simpl in Hnodup; [contradiction|].
  apply wf_branch.
  - exact Hdepth.
  - eapply N.le_lt_trans; [apply N.ldiff_le_l|exact Hbound].
  - intro Hzero.
    assert (Hpairs : Forall2
      (fun routed inserted => inserted <> Empty /\
        wf E hash seed (S depth) (prefix ++ [routed]) inserted)
      (before ++ after) (children_before ++ children_after)).
    { now apply Forall2_app. }
    assert (Hoccupied : occupied_slots (N.ldiff bitmap (bitmap_bit slot)) <> []).
    { intro Hempty. rewrite Hnew in Hempty. rewrite Hempty in Hpairs.
      inversion Hpairs. now apply Hdense_nonempty. }
    rewrite Hzero, occupied_slots_empty in Hoccupied. contradiction.
  - rewrite <- Hremove, dense_remove_length_hit.
    + rewrite Hlength, (@popcount_ldiff_bit_present bitmap slot Hslot Hpresent).
      reflexivity.
    + rewrite Hchildren_eq, <- Hrank, <- Hbefore_length.
      rewrite length_app. simpl. lia.
  - rewrite Hnew, Hdense. now apply Forall2_app.
  - change (NoDupA (binding_equiv E) (bindings head ++ flat_map bindings tail)).
    exact Hnodup.
Qed.

Lemma remove_tree_branch_child_wf_removed_nonempty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool) child,
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    remove_tree eqb fuel (S depth) full_hash key child = Empty ->
    dense_remove (rank bitmap (chunk full_hash depth)) children <> [] ->
    NoDupA (binding_equiv E)
      (bindings (Branch
        (N.ldiff bitmap (bitmap_bit (chunk full_hash depth)))
        (dense_remove (rank bitmap (chunk full_hash depth)) children))) ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children
    eqb child Hwf Hpresent Hchild Hremove Hremaining Hnodup.
  rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
    children Hpresent Hchild).
  rewrite Hremove.
  unfold branch_remove.
  destruct (dense_remove (rank bitmap (chunk full_hash depth)) children)
    as [|head tail] eqn:Hdense; [contradiction|].
  rewrite <- Hdense.
  apply wf_branch_remove_present_nonempty with
    (slot := chunk full_hash depth); try assumption.
  - apply chunk_bound.
  - now rewrite Hdense.
  - rewrite Hdense. exact Hnodup.
Qed.

Lemma remove_tree_branch_child_wf_singleton_empty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool) child,
    wf E hash seed depth prefix (Branch bitmap children) ->
    length children = 1 ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    remove_tree eqb fuel (S depth) full_hash key child = Empty ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children
    eqb child Hwf Hlength Hpresent Hchild Hremove.
  rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
    children Hpresent Hchild).
  rewrite Hremove.
  rewrite (@branch_remove_wf_singleton_empty K Seed A E hash seed depth prefix
    bitmap children (chunk full_hash depth) Hwf Hlength (chunk_bound _ _) Hpresent).
  apply wf_empty.
Qed.

Lemma remove_tree_branch_dense_missing :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = None ->
    remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children) =
    Branch bitmap children.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children Hpresent Hmissing.
  cbn [remove_tree]. now rewrite Hpresent, Hmissing.
Qed.

Lemma remove_tree_branch_dense_missing_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = None ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children eqb
    Hwf Hpresent Hmissing.
  rewrite (remove_tree_branch_dense_missing eqb fuel depth full_hash key
    bitmap children Hpresent Hmissing).
  exact Hwf.
Qed.

Lemma bindings_dense_insert :
  forall (K A : Type) index (child : tree K A) children (entry : K * A),
    In entry (flat_map bindings (dense_insert index child children)) <->
    In entry (bindings child) \/ In entry (flat_map bindings children).
Proof.
  intros K A index child children entry.
  split.
  - intro Hin. apply in_flat_map in Hin.
    destruct Hin as [node [Hnode Hin]].
    apply dense_insert_in in Hnode. destruct Hnode as [Hnode|Hnode].
    + subst node. now left.
    + right. apply in_flat_map. now exists node.
  - intro Hin. destruct Hin as [Hin|Hin].
    + apply in_flat_map. exists child. split; auto.
      apply dense_insert_in. now left.
    + apply in_flat_map in Hin. destruct Hin as [node [Hnode Hin]].
      apply in_flat_map. exists node. split; auto.
      apply dense_insert_in. now right.
Qed.

Lemma bindings_branch_insert :
  forall (K A : Type) bitmap slot (child : tree K A) children (entry : K * A),
    In entry (bindings (branch_insert bitmap slot child children)) <->
    In entry (bindings child) \/ In entry (bindings (Branch bitmap children)).
Proof.
  intros K A bitmap slot child children entry.
  unfold branch_insert. simpl.
  apply bindings_dense_insert.
Qed.

Lemma bindings_dense_remove_in :
  forall (K A : Type) index children (entry : K * A),
    In entry (flat_map bindings (dense_remove index children)) ->
    In entry (flat_map bindings children).
Proof.
  intros K A index children entry Hin.
  apply in_flat_map in Hin. destruct Hin as [node [Hnode Hin]].
  apply dense_remove_in in Hnode.
  apply in_flat_map. now exists node.
Qed.

Inductive list_subseq {A : Type} : list A -> list A -> Prop :=
| list_subseq_nil : list_subseq [] []
| list_subseq_keep : forall item kept source,
    list_subseq kept source -> list_subseq (item :: kept) (item :: source)
| list_subseq_drop : forall item kept source,
    list_subseq kept source -> list_subseq kept (item :: source).

Lemma list_subseq_in :
  forall A (kept source : list A) item,
    list_subseq kept source -> In item kept -> In item source.
Proof.
  intros A kept source item Hsub. induction Hsub; intro Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin]; [now left|now right; apply IHHsub].
  - now right; apply IHHsub.
Qed.

Lemma list_subseq_InA :
  forall A (R : A -> A -> Prop) kept source item,
    list_subseq kept source -> InA R item kept -> InA R item source.
Proof.
  intros A R kept source item Hsub. induction Hsub; intro Hin.
  - inversion Hin.
  - inversion Hin; subst.
    + constructor. assumption.
    + constructor 2. now apply IHHsub.
  - constructor 2. now apply IHHsub.
Qed.

Lemma list_subseq_refl :
  forall A (items : list A), list_subseq items items.
Proof.
  intros A items. induction items as [|item items IH].
  - constructor.
  - apply list_subseq_keep. exact IH.
Qed.

Lemma list_subseq_app_r :
  forall A (left right : list A), list_subseq right (left ++ right).
Proof.
  intros A left. induction left as [|item left IH]; intro right; simpl.
  - apply list_subseq_refl.
  - apply list_subseq_drop. apply IH.
Qed.

Lemma list_subseq_app_l :
  forall A (left kept source : list A),
    list_subseq kept source -> list_subseq (left ++ kept) (left ++ source).
Proof.
  intros A left. induction left as [|item left IH]; intros kept source Hsub;
    simpl.
  - exact Hsub.
  - apply list_subseq_keep. now apply IH.
Qed.

Lemma list_subseq_app_r_lift :
  forall A (kept source right : list A),
    list_subseq kept source ->
    list_subseq (kept ++ right) (source ++ right).
Proof.
  intros A kept source right Hsub. induction Hsub; simpl.
  - apply list_subseq_refl.
  - apply list_subseq_keep. exact IHHsub.
  - apply list_subseq_drop. exact IHHsub.
Qed.

Lemma list_subseq_length_le :
  forall A (kept source : list A),
    list_subseq kept source -> length kept <= length source.
Proof.
  intros A kept source Hsub. induction Hsub; simpl; lia.
Qed.

Lemma NoDupA_list_subseq :
  forall A (R : A -> A -> Prop) kept source,
    list_subseq kept source -> NoDupA R source -> NoDupA R kept.
Proof.
  intros A R kept source Hsub. induction Hsub; intro Hnodup.
  - constructor.
  - inversion Hnodup as [|item' source' Hnot Htail]; subst.
    constructor.
    + intro Hin. apply Hnot. now apply list_subseq_InA with (kept := kept).
    + now apply IHHsub.
  - inversion Hnodup as [|item' source' Hnot Htail]; subst.
    now apply IHHsub.
Qed.

Lemma InA_transport_left :
  forall A (R : A -> A -> Prop) x y items,
    Equivalence R -> R x y -> InA R y items -> InA R x items.
Proof.
 intros A R x y items [_ Hsym Htrans] Hxy Hin.
 apply (proj2 (InA_alt R x items)).
 apply (proj1 (InA_alt R y items)) in Hin.
 destruct Hin as [stored [Hy Hin]].
 exists stored. split; [eapply Htrans; eauto|exact Hin].
Qed.

Lemma NoDupA_app_inv :
  forall A (R : A -> A -> Prop) left right,
    Equivalence R -> NoDupA R (left ++ right) ->
    NoDupA R left /\ NoDupA R right /\
      (forall item, InA R item left -> InA R item right -> False).
Proof.
 intros A R left. induction left as [|head left IH]; intros right
   Hequiv Hnodup.
 - destruct Hequiv as [Href Hsym Htrans].
   pose proof (Build_Equivalence R Href Hsym Htrans) as Hequiv.
   simpl in Hnodup. split; [constructor|]. split; [exact Hnodup|].
   intros item Hin. inversion Hin.
 - simpl in Hnodup. inversion Hnodup as [|head' remaining Hfresh Htail]; subst.
   destruct Hequiv as [Href Hsym Htrans].
   pose proof (Build_Equivalence R Href Hsym Htrans) as Hequiv.
   destruct (IH right Hequiv Htail) as [Hleft [Hright Hcross]].
   split.
   + apply NoDupA_cons.
     * intro Hin. apply Hfresh.
       apply (proj2 (InA_app_iff R left right head)). now left.
     * exact Hleft.
   + split; [exact Hright|].
     intros item Hinleft Hinright.
     apply (proj1 (InA_cons R item head left)) in Hinleft.
     destruct Hinleft as [Hhead|Hinleft].
     * apply Hfresh.
       apply (proj2 (InA_app_iff R left right head)). right.
       apply (@InA_transport_left A R head item right Hequiv).
       -- apply Hsym. exact Hhead.
       -- exact Hinright.
     * eapply Hcross; eauto.
Qed.

Lemma NoDupA_insert_between :
  forall A (R : A -> A -> Prop) left right item,
    Equivalence R -> NoDupA R (left ++ right) ->
    ~ InA R item (left ++ right) ->
    NoDupA R (left ++ [item] ++ right).
Proof.
 intros A R left right item Hequiv Hnodup Hfresh.
 destruct Hequiv as [Href Hsym Htrans].
 pose proof (Build_Equivalence R Href Hsym Htrans) as Hequiv.
 destruct (@NoDupA_app_inv A R left right Hequiv Hnodup)
   as [Hleft [Hright Hcross]].
 apply NoDupA_app; [exact Hequiv|exact Hleft| |].
 apply NoDupA_cons.
 - intro Hin. apply Hfresh.
   apply (proj2 (InA_app_iff R left right item)). right. exact Hin.
 - exact Hright.
 - intros candidate Hcandidate Htail.
   apply (proj1 (InA_cons R candidate item right)) in Htail.
   destruct Htail as [Hitem|Hright_candidate].
   + apply Hfresh.
     apply (proj2 (InA_app_iff R left right item)). left.
     exact (@InA_transport_left A R item candidate left Hequiv
       (Hsym _ _ Hitem) Hcandidate).
   + eapply Hcross; eauto.
Qed.

Lemma NoDupA_replace_between :
  forall A (R : A -> A -> Prop) before old replacement after,
    Equivalence R ->
    NoDupA R (before ++ old ++ after) ->
    NoDupA R replacement ->
    (forall entry, InA R entry before -> InA R entry replacement -> False) ->
    (forall entry, InA R entry replacement -> InA R entry after -> False) ->
    NoDupA R (before ++ replacement ++ after).
Proof.
  intros A R before old replacement after Hequiv Horiginal Hreplacement
    Hbefore_replacement Hreplacement_after.
  destruct (@NoDupA_app_inv A R before (old ++ after) Hequiv Horiginal)
    as [Hbefore [Hold_after Hbefore_after]].
  destruct (@NoDupA_app_inv A R old after Hequiv Hold_after)
    as [_ [Hafter _]].
  apply NoDupA_app; [exact Hequiv|exact Hbefore| |].
  - apply NoDupA_app; [exact Hequiv|exact Hreplacement|exact Hafter|].
    exact Hreplacement_after.
  - intros entry Hinbefore Hinreplacement_after.
    apply (proj1 (InA_app_iff R replacement after entry)) in Hinreplacement_after.
    destruct Hinreplacement_after as [Hinreplacement|Hinafter].
    + eapply Hbefore_replacement; eauto.
    + eapply Hbefore_after; [exact Hinbefore|].
      apply (proj2 (InA_app_iff R old after entry)). now right.
Qed.

Lemma bindings_dense_insert_split :
  forall (K A : Type) index (child : tree K A) children,
    exists before after,
      flat_map bindings children = before ++ after /\
      flat_map bindings (dense_insert index child children) =
        before ++ bindings child ++ after.
Proof.
 intros K A index. induction index as [|index IH]; intros child children.
 - exists [], (flat_map bindings children). simpl. split; reflexivity.
 - destruct children as [|head tail].
   + exists [], []. simpl. split; reflexivity.
   + destruct (IH child tail) as [before [after [Hbefore Hinsert]]].
     exists (bindings head ++ before), after. simpl.
     rewrite Hbefore, Hinsert. repeat rewrite app_assoc. split; reflexivity.
Qed.

Lemma bindings_dense_replace_split :
  forall (K A : Type) index (replacement child : tree K A) children,
    dense_get index children = Some child ->
    exists before after,
      flat_map bindings children = before ++ bindings child ++ after /\
      flat_map bindings (dense_replace index replacement children) =
        before ++ bindings replacement ++ after.
Proof.
  intros K A index. induction index as [|index IH]; intros replacement child
    children Hget; destruct children as [|head tail].
  - unfold dense_get in Hget. discriminate.
  - unfold dense_get in Hget. simpl in Hget. inversion Hget; subst child.
    exists [], (flat_map bindings tail). simpl. split; reflexivity.
  - unfold dense_get in Hget. discriminate.
  - unfold dense_get in Hget. simpl in Hget.
    destruct (IH replacement child tail Hget) as [before [after [Hbefore Hreplace]]].
    exists (bindings head ++ before), after. simpl.
    rewrite Hbefore, Hreplace. repeat rewrite app_assoc. split; reflexivity.
Qed.

Lemma bindings_dense_get_split :
  forall (K A : Type) index (children : list (tree K A)) child,
    dense_get index children = Some child ->
    exists before after,
      children = before ++ child :: after /\
      flat_map bindings children =
        flat_map bindings before ++ bindings child ++ flat_map bindings after.
Proof.
  intros K A index. induction index as [|index IH]; intros children child Hget;
    destruct children as [|head tail].
  - unfold dense_get in Hget. discriminate.
  - unfold dense_get in Hget. simpl in Hget. inversion Hget; subst child.
    exists [], tail. simpl. split; reflexivity.
  - unfold dense_get in Hget. discriminate.
  - unfold dense_get in Hget. simpl in Hget.
    destruct (IH tail child Hget) as [before [after [Hchildren Hbindings]]].
    exists (head :: before), after. split.
    + simpl. now rewrite Hchildren.
    + simpl. rewrite Hbindings. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma dense_replace_split :
  forall A index (replacement child : A) children,
    dense_get index children = Some child ->
    exists before after,
      children = before ++ child :: after /\
      dense_replace index replacement children = before ++ replacement :: after.
Proof.
  intros A index. induction index as [|index IH]; intros replacement child
    children Hget; destruct children as [|head tail].
  - unfold dense_get in Hget. discriminate.
  - unfold dense_get in Hget. simpl in Hget. inversion Hget; subst child.
    exists [], tail. simpl. split; reflexivity.
  - unfold dense_get in Hget. discriminate.
  - unfold dense_get in Hget. simpl in Hget.
    destruct (IH replacement child tail Hget) as [before [after [Hchildren Hreplace]]].
    exists (head :: before), after. simpl. rewrite Hreplace, Hchildren.
    split; reflexivity.
Qed.

Lemma dense_replace_at_split :
  forall A index (before after : list A) old replacement,
    length before = index ->
    dense_replace index replacement (before ++ old :: after) =
      before ++ replacement :: after.
Proof.
  intros A index before. revert index.
  induction before as [|head before IH]; intros index after old replacement Hlength.
  - destruct index; simpl; [reflexivity|discriminate].
  - destruct index as [|index]; simpl in Hlength; [discriminate|].
    simpl. f_equal. apply IH. lia.
Qed.

Lemma Forall2_dense_get_split :
  forall A B (R : A -> B -> Prop) index slots children slot child,
    Forall2 R slots children ->
    nth_error slots index = Some slot ->
    dense_get index children = Some child ->
    exists slots_before slots_after children_before children_after,
      slots = slots_before ++ slot :: slots_after /\
      children = children_before ++ child :: children_after /\
      length slots_before = index /\
      Forall2 R slots_before children_before /\
      R slot child /\
      Forall2 R slots_after children_after.
Proof.
  intros A B R index. induction index as [|index IH];
    intros slots children slot child Hpaired Hslot Hchild;
    destruct slots as [|head_slot slots]; destruct children as [|head_child children].
  - discriminate.
  - inversion Hpaired.
  - inversion Hpaired.
  - inversion Hpaired as [|slot' child' slots' children' Hhead Htail]; subst.
    simpl in Hslot, Hchild. inversion Hslot; inversion Hchild; subst.
    exists [], slots, [], children. simpl. repeat split; auto.
  - discriminate.
  - inversion Hpaired.
  - inversion Hpaired.
  - inversion Hpaired as [|slot' child' slots' children' Hhead Htail]; subst.
    simpl in Hslot, Hchild.
    destruct (IH slots children slot child Htail Hslot Hchild)
      as [slots_before [slots_after [children_before [children_after
        [Hslots [Hchildren [Hlength [Hbefore [Hselected Hafter]]]]]]]]].
    exists (head_slot :: slots_before), slots_after,
      (head_child :: children_before), children_after.
    simpl. rewrite Hslots, Hchildren. repeat split; try reflexivity;
      try (simpl; lia).
    + constructor; assumption.
    + exact Hselected.
    + exact Hafter.
Qed.

Lemma NoDup_before_selected :
  forall A (before after : list A) selected candidate,
    NoDup (before ++ selected :: after) ->
    In candidate before -> selected <> candidate.
Proof.
  intros A before. induction before as [|head before IH];
    intros after selected candidate Hnodup Hin.
  - contradiction.
  - simpl in Hin. inversion Hnodup as [|head' tail Hfresh Htail]; subst.
    destruct Hin as [Hcandidate|Hin].
    + subst candidate. intro Heq. subst selected.
      apply Hfresh. apply in_app_iff. right. now left.
    + apply IH with (after := after); assumption.
Qed.

Lemma NoDup_after_selected :
  forall A (before after : list A) selected candidate,
    NoDup (before ++ selected :: after) ->
    In candidate after -> selected <> candidate.
Proof.
  intros A before after selected candidate Hnodup Hin Heq. subst candidate.
  apply NoDup_app_remove_l with (l := before) in Hnodup.
  inversion Hnodup as [|selected' after' Hfresh Htail]; subst.
  apply Hfresh. exact Hin.
Qed.

Lemma bindings_branch_insert_leaf_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) depth prefix bitmap children slot full_hash key (value : A),
    Equivalence E ->
    wf E hash seed depth prefix (Branch bitmap children) ->
    ~ InA (binding_equiv E) (key, value)
        (bindings (Branch bitmap children)) ->
    NoDupA (binding_equiv E)
      (bindings (branch_insert bitmap slot (Leaf full_hash key value) children)).
Proof.
 intros K Seed A E hash seed depth prefix bitmap children slot full_hash key value
   Hequiv Hwf Hfresh.
 destruct (@bindings_dense_insert_split K A (rank bitmap slot)
   (Leaf full_hash key value) children) as [before [after [Hbefore Hinsert]]].
 pose proof (@wf_bindings_nodup K Seed A E hash seed depth prefix
   (Branch bitmap children) Hwf) as Hnodup.
 unfold branch_insert. simpl.
 rewrite Hinsert.
 apply NoDupA_insert_between with (R := binding_equiv E).
 - now apply binding_equiv_equiv.
 - rewrite <- Hbefore. exact Hnodup.
 - rewrite <- Hbefore. exact Hfresh.
Qed.

Lemma set_tree_branch_slot_absent_wf_leaf_fresh :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K) (value : A)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool),
    Equivalence E ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = false ->
    length prefix = depth ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix
      (set_tree eqb (S fuel) depth full_hash key value
        (Branch bitmap children)).
Proof.
 intros K Seed A E hash seed fuel depth prefix full_hash key value bitmap
   children eqb Hequiv Hcongruent Hwf Habsent Hlength Hhash Hbound Hprefix.
 eapply (@set_tree_branch_slot_absent_wf_leaf K Seed A E hash seed fuel depth
   prefix full_hash key value bitmap children eqb);
   try assumption.
 eapply (@bindings_branch_insert_leaf_nodup K Seed A E hash seed depth prefix
   bitmap children (chunk full_hash depth) full_hash key value).
 - exact Hequiv.
 - exact Hwf.
 - eapply (@wf_branch_slot_absent_fresh K Seed A E hash seed depth prefix
     bitmap children full_hash key value).
   + exact Hequiv.
   + exact Hcongruent.
   + exact Hlength.
   + exact Hhash.
   + exact Hwf.
   + exact Habsent.
Qed.

Lemma flat_map_dense_remove_subseq :
  forall (K A : Type) index (children : list (tree K A)),
    list_subseq (flat_map bindings (dense_remove index children))
      (flat_map bindings children).
Proof.
  intros K A index. induction index as [|index IH]; intros children.
  - destruct children as [|child children]; simpl.
    + constructor.
    + apply list_subseq_app_r.
  - destruct children as [|child children]; simpl.
    + constructor.
    + apply list_subseq_app_l. apply IH.
Qed.

Lemma flat_map_dense_replace_subseq :
  forall (K A : Type) index (old child : tree K A) children,
    dense_get index children = Some old ->
    list_subseq (bindings child) (bindings old) ->
    list_subseq (flat_map bindings (dense_replace index child children))
      (flat_map bindings children).
Proof.
  intros K A index. induction index as [|index IH];
    intros old child children Hget Hsub.
  - destruct children as [|head tail]; simpl in Hget.
    + discriminate.
    + inversion Hget; subst old. simpl.
      apply list_subseq_app_r_lift. exact Hsub.
  - destruct children as [|head tail]; simpl in Hget.
    + discriminate.
    + simpl. apply list_subseq_app_l.
      apply IH with (old := old); assumption.
Qed.

Lemma bucket_remove_subseq :
  forall (K A : Type) (eqb : K -> K -> bool) key
         (entries : list (K * A)),
    list_subseq (bucket_remove eqb key entries) entries.
Proof.
  intros K A eqb key entries.
  induction entries as [|[stored value] tail IH]; simpl.
  - constructor.
  - destruct (eqb key stored) eqn:Hstored.
    + exact (@list_subseq_app_r (K * A) [(stored, value)] tail).
    + apply list_subseq_keep. exact IH.
Qed.

Lemma bindings_branch_remove_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) depth prefix bitmap (children : list (tree K A)) slot,
    wf E hash seed depth prefix (Branch bitmap children) ->
    NoDupA (binding_equiv E) (bindings (branch_remove bitmap slot children)).
Proof.
  intros K Seed A E hash seed depth prefix bitmap children slot Hwf.
  inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength Hchildren
    Hnodup]; subst.
  change (NoDupA (binding_equiv E) (flat_map bindings children)) in Hnodup.
  unfold branch_remove.
  destruct (dense_remove (rank bitmap slot) children) as [|child remaining]
    eqn:Hremove; simpl.
  - constructor.
  - apply NoDupA_list_subseq with (source := flat_map bindings children).
    + change (list_subseq (flat_map bindings (child :: remaining))
        (flat_map bindings children)).
      rewrite <- Hremove. apply flat_map_dense_remove_subseq.
    + exact Hnodup.
Qed.

Lemma wf_branch_remove_present_nonempty_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (depth : nat) (prefix : list N) (bitmap : N)
         (children : list (tree K A)) (slot : N),
    wf E hash seed depth prefix (Branch bitmap children) ->
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = true ->
    dense_remove (rank bitmap slot) children <> [] ->
    wf E hash seed depth prefix
      (Branch (N.ldiff bitmap (bitmap_bit slot))
        (dense_remove (rank bitmap slot) children)).
Proof.
  intros K Seed A E hash seed depth prefix bitmap children slot Hwf Hslot
    Hpresent Hremaining.
  apply wf_branch_remove_present_nonempty with (slot := slot);
    try assumption.
  pose proof (@bindings_branch_remove_nodup K Seed A E hash seed depth prefix
    bitmap children slot Hwf) as Hnodup.
  unfold branch_remove in Hnodup.
  destruct (dense_remove (rank bitmap slot) children) as [|head tail] eqn:Hremove;
    simpl in Hnodup; [contradiction|].
  exact Hnodup.
Qed.

Lemma remove_tree_branch_child_wf_removed_nonempty_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool) child,
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    remove_tree eqb fuel (S depth) full_hash key child = Empty ->
    dense_remove (rank bitmap (chunk full_hash depth)) children <> [] ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children
    eqb child Hwf Hpresent Hchild Hremove Hremaining.
  rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
    children Hpresent Hchild).
  rewrite Hremove.
  unfold branch_remove.
  destruct (dense_remove (rank bitmap (chunk full_hash depth)) children)
    as [|head tail] eqn:Hdense; [contradiction|].
  rewrite <- Hdense.
  apply wf_branch_remove_present_nonempty_wf with
    (slot := chunk full_hash depth); try assumption.
  - apply chunk_bound.
  - now rewrite Hdense.
Qed.

Lemma bindings_branch_remove_in :
  forall (K A : Type) bitmap slot children (entry : K * A),
    In entry (bindings (branch_remove bitmap slot children)) ->
    In entry (bindings (Branch bitmap children)).
Proof.
  intros K A bitmap slot children entry Hin.
  unfold branch_remove in Hin.
  remember (dense_remove (rank bitmap slot) children) as remaining.
  destruct remaining as [|child remaining]; simpl in Hin.
  - contradiction.
  - simpl. apply (bindings_dense_remove_in (rank bitmap slot) children entry).
    change (In entry (flat_map bindings (child :: remaining))) in Hin.
    rewrite Heqremaining in Hin. exact Hin.
Qed.

Lemma bindings_branch_replace_in :
  forall (K A : Type) bitmap slot (child : tree K A) children (entry : K * A),
    rank bitmap slot < length children ->
    In entry (bindings (branch_replace bitmap slot child children)) ->
    In entry (bindings child) \/ In entry (bindings (Branch bitmap children)).
Proof.
  intros K A bitmap slot child children entry Hbound Hin.
  unfold branch_replace in Hin. simpl in Hin.
  apply in_flat_map in Hin. destruct Hin as [node [Hnode Hin]].
  apply (@dense_replace_in (tree K A) (rank bitmap slot) child children node Hbound) in Hnode.
  destruct Hnode as [Hnode|Hnode].
  - subst node. now left.
  - right. apply in_flat_map. now exists node.
Qed.

Lemma wf_empty_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed),
    @wf K Seed A E hash seed 0 [] Empty.
Proof. intros. constructor. Qed.

Lemma wf_leaf_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) full_hash key (value : A),
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    @wf K Seed A E hash seed 0 [] (Leaf full_hash key value).
Proof.
  intros K Seed A E hash seed full_hash key value Hhash Hbound.
  apply wf_leaf; auto. exact I.
Qed.

Section EmptyOperationInvariant.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

Lemma set_tree_empty_wf :
    forall fuel depth prefix full_hash key (value : A) (eqb : K -> K -> bool),
      entry_matches hash seed full_hash depth prefix (key, value) ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value Empty).
  Proof.
    intros fuel depth prefix full_hash key value eqb Hentry.
    destruct Hentry as [Hhash [Hbound Hprefix]].
    destruct fuel; cbn [set_tree]; eapply wf_leaf; eauto.
  Qed.

Lemma remove_tree_empty_wf :
    forall fuel depth prefix full_hash key (eqb : K -> K -> bool),
      wf E hash seed depth prefix
        (remove_tree eqb fuel depth full_hash key (@Empty K A)).
  Proof. intros. destruct fuel; cbn [remove_tree]; apply wf_empty. Qed.

End EmptyOperationInvariant.

Lemma get_tree_leaf_same :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    eqb key key = true ->
    get_tree eqb fuel depth full_hash key (Leaf full_hash key value) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value Heqb.
  destruct fuel; simpl; now rewrite N.eqb_refl, Heqb.
Qed.

Lemma get_tree_empty :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (query : K),
    get_tree eqb fuel depth full_hash query (@Empty K A) = None.
Proof. intros. destruct fuel; reflexivity. Qed.

Lemma get_tree_binding_sound :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash query
         (t : tree K A) value,
    get_tree eqb fuel depth full_hash query t = Some value ->
    exists stored,
      In (stored, value) (bindings t) /\ eqb query stored = true.
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash query t value Hget;
    destruct t as [|stored_hash stored stored_value|stored_hash entries|bitmap children].
  - discriminate.
  - cbn [get_tree] in Hget.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash; [|discriminate].
    destruct (eqb query stored) eqn:Hmatch; [|discriminate].
    inversion Hget; subst value.
    exists stored. split; [now left|exact Hmatch].
  - cbn [get_tree] in Hget.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash; [|discriminate].
    now apply bucket_get_sound in Hget.
  - discriminate.
  - discriminate.
  - cbn [get_tree] in Hget.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash; [|discriminate].
    destruct (eqb query stored) eqn:Hmatch; [|discriminate].
    inversion Hget; subst value.
    exists stored. split; [now left|exact Hmatch].
  - cbn [get_tree] in Hget.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash; [|discriminate].
    now apply bucket_get_sound in Hget.
  - cbn [get_tree] in Hget.
    destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hroute;
      [|discriminate].
    destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild; [|discriminate].
    destruct (IH (S depth) full_hash query child value Hget)
      as [stored [Hbinding Hmatch]].
    exists stored. split; [|exact Hmatch].
    cbn [bindings]. apply in_flat_map.
    exists child. split.
    + unfold dense_get in Hchild.
      now apply nth_error_In with (n := rank bitmap (chunk full_hash depth)).
    + exact Hbinding.
Qed.

Lemma get_binding_sound :
  forall (K Seed A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         (hash : Seed -> K -> N) query (m : table K Seed A) value,
    (forall first second, eqb first second = true <-> E first second) ->
    get eqb hash query m = Some value ->
    exists stored,
      In (stored, value) (elements m) /\ E query stored.
Proof.
  intros K Seed A E eqb hash query [seed root] value Heqb Hget.
  change (get_tree eqb branch_levels 0 (hash seed query) query root = Some value)
    in Hget.
  destruct (@get_tree_binding_sound K A eqb branch_levels 0 (hash seed query)
    query root value Hget) as [stored [Hbinding Hmatch]].
  exists stored. split; [exact Hbinding|].
  now apply (proj1 (Heqb query stored)).
Qed.

Lemma get_tree_leaf_binding_complete :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (query stored : K) (value : A) stored_hash,
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second -> hash seed first = hash seed second) ->
    full_hash = hash seed query ->
    wf E hash seed depth prefix (Leaf stored_hash stored value) ->
    E query stored ->
    get_tree eqb fuel depth full_hash query
      (Leaf stored_hash stored value) = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash query stored
    value stored_hash Heqb Hcongruent Hfull Hwf Hrelated.
  assert (Hstored : stored_hash = hash seed stored).
  { inversion Hwf; assumption. }
  assert (Hsame : full_hash = stored_hash).
  { rewrite Hfull, Hstored. apply Hcongruent. exact Hrelated. }
  assert (Hmatch : eqb query stored = true).
  { apply (proj2 (Heqb query stored)). exact Hrelated. }
  destruct fuel; cbn [get_tree]; now rewrite Hsame, N.eqb_refl, Hmatch.
Qed.

Lemma get_tree_collision_binding_complete :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (query stored : K) (value : A) stored_hash entries,
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second -> hash seed first = hash seed second) ->
    full_hash = hash seed query ->
    wf E hash seed depth prefix (Collision stored_hash entries) ->
    In (stored, value) entries ->
    E query stored ->
    get_tree eqb fuel depth full_hash query
      (Collision stored_hash entries) = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash query stored
    value stored_hash entries Hequiv Heqb Hcongruent Hfull Hwf Hin Hrelated.
  assert (Hstored : stored_hash = hash seed stored).
  { eapply (@collision_binding_hash K Seed A E hash seed depth prefix
      stored_hash entries (stored, value)); eauto. }
  assert (Hsame : full_hash = stored_hash).
  { rewrite Hfull, Hstored. apply Hcongruent. exact Hrelated. }
  assert (Hnodup : NoDupA (fun left right : K * A => E (fst left) (fst right))
    entries).
  { inversion Hwf; subst. exact H5. }
  destruct fuel; cbn [get_tree]; rewrite Hsame, N.eqb_refl.
  - eapply bucket_get_complete; eauto.
  - eapply bucket_get_complete; eauto.
Qed.

Lemma get_tree_binding_complete :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (query stored : K) (value : A) (t : tree K A),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second -> hash seed first = hash seed second) ->
    full_hash = hash seed query ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix t ->
    In (stored, value) (bindings t) ->
    E query stored ->
    get_tree eqb fuel depth full_hash query t = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash query stored value t
    Hfuel Hlength Hequiv Heqb Hcongruent Hfull Hbound Hprefix Hwf Hin Hrelated;
    destruct t as [|stored_hash leaf_key leaf_value|stored_hash entries|bitmap children].
  - contradiction.
  - simpl in Hin. destruct Hin as [Hin|[]]. inversion Hin; subst leaf_key leaf_value.
    eapply get_tree_leaf_binding_complete; eauto.
  - eapply get_tree_collision_binding_complete; eauto.
  - exfalso.
    eapply (@wf_branch_impossible_at_or_beyond_limit K Seed A E hash seed
      depth prefix bitmap children).
    + lia.
    + exact Hwf.
  - contradiction.
  - simpl in Hin. destruct Hin as [Hin|[]]. inversion Hin; subst leaf_key leaf_value.
    eapply get_tree_leaf_binding_complete; eauto.
  - eapply get_tree_collision_binding_complete; eauto.
  - assert (Hentry_hash : full_hash = hash seed (fst (stored, value))).
    { simpl. rewrite Hfull. apply Hcongruent. exact Hrelated. }
    assert (Hpresent : bitmap_has bitmap (chunk full_hash depth) = true).
    { rewrite Hentry_hash.
      eapply wf_branch_binding_routes; eauto. }
    destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hpresent)
      as [child [Hchild [Hchildnonempty Hchildwf]]].
    assert (Hinchild : In (stored, value) (bindings child)).
    { eapply wf_branch_dense_get_binding; eauto.
      rewrite Hentry_hash. reflexivity. }
    assert (Hnextlength : length (prefix ++ [chunk full_hash depth]) = S depth).
    { rewrite app_length, Hlength. cbn. lia. }
    assert (Hnextprefix : prefix_matches full_hash (S depth)
      (prefix ++ [chunk full_hash depth])).
    { apply prefix_matches_append_slot; assumption. }
    cbn [get_tree]. rewrite Hpresent, Hchild.
    eapply IH; eauto; lia.
Qed.

Lemma get_binding_complete :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query stored (value : A) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    In (stored, value) (elements m) ->
    E query stored ->
    get eqb hash query m = Some value.
Proof.
  intros K Seed A E hash eqb query stored value [seed root] Hequiv Heqb
    Hcongruent Hbound Hwf Hin Hrelated.
  change (get_tree eqb branch_levels 0 (hash seed query) query root = Some value).
  eapply get_tree_binding_complete; eauto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma get_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query (value : A) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    (get eqb hash query m = Some value <->
      exists stored, In (stored, value) (elements m) /\ E query stored).
Proof.
  intros K Seed A E hash eqb query value m Hequiv Heqb Hcongruent Hbound Hwf.
  split.
  - intro Hget. eapply get_binding_sound; eauto.
  - intros [stored [Hin Hrelated]].
    eapply get_binding_complete; eauto.
Qed.

Lemma mem_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    (mem eqb hash query m = true <->
      exists stored value, In (stored, value) (elements m) /\ E query stored).
Proof.
  intros K Seed A E hash eqb query m Hequiv Heqb Hcongruent Hbound Hwf.
  split.
  - intro Hmem. apply mem_spec in Hmem.
    destruct Hmem as [value Hget].
    apply (@get_binding_iff K Seed A E hash eqb query value m
      Hequiv Heqb Hcongruent Hbound Hwf) in Hget.
    destruct Hget as [stored [Hin Hrelated]].
    now exists stored, value.
  - intros [stored [value [Hin Hrelated]]].
    apply mem_spec. exists value.
    apply (@get_binding_iff K Seed A E hash eqb query value m
      Hequiv Heqb Hcongruent Hbound Hwf).
    now exists stored.
Qed.

Lemma get_tree_leaf_other_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash stored_hash
         key stored (value : A),
    full_hash <> stored_hash ->
    get_tree eqb fuel depth full_hash key (Leaf stored_hash stored value) = None.
Proof.
  intros K A eqb fuel depth full_hash stored_hash key stored value Hneq.
  destruct fuel; simpl; apply N.eqb_neq in Hneq; now rewrite Hneq.
Qed.

Lemma get_tree_leaf_other_key :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash query stored
         (value : A),
    eqb query stored = false ->
    get_tree eqb fuel depth full_hash query (Leaf full_hash stored value) = None.
Proof.
  intros K A eqb fuel depth full_hash query stored value Heqb.
  destruct fuel; cbn [get_tree]; now rewrite N.eqb_refl, Heqb.
Qed.

Lemma set_tree_leaf_replaces_representative :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key stored
         (old value : A),
    eqb key stored = true ->
    set_tree eqb fuel depth full_hash key value (Leaf full_hash stored old) =
    Leaf full_hash stored value.
Proof.
  intros K A eqb fuel depth full_hash key stored old value Heqb.
  destruct fuel; cbn [set_tree]; now rewrite Heqb.
Qed.

Section LeafUpdateInvariant.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

Lemma set_tree_leaf_replacement_wf :
    forall fuel depth prefix full_hash key stored (old_value value : A)
           (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Leaf full_hash stored old_value) ->
      eqb key stored = true ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Leaf full_hash stored old_value)).
  Proof.
    intros fuel depth prefix full_hash key stored old_value value eqb Hwf Hmatch.
    rewrite set_tree_leaf_replaces_representative by exact Hmatch.
    inversion Hwf; subst; eauto using wf_leaf.
  Qed.

Lemma set_tree_leaf_collision_wf :
    forall fuel depth prefix full_hash key stored (old_value value : A)
           (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Leaf full_hash stored old_value) ->
      entry_matches hash seed full_hash depth prefix (key, value) ->
      eqb key stored = false ->
      ~ E stored key ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Leaf full_hash stored old_value)).
  Proof.
    intros fuel depth prefix full_hash key stored old_value value eqb Hwf Hentry
      Hdifferent Hdistinct.
    assert (Hstored : entry_matches hash seed full_hash depth prefix (stored, old_value)).
    { inversion Hwf; subst. repeat split; assumption. }
    assert (Hset :
      set_tree eqb fuel depth full_hash key value
        (Leaf full_hash stored old_value) =
      Collision full_hash [(stored, old_value); (key, value)]).
    { destruct fuel; cbn [set_tree]; now rewrite Hdifferent, N.eqb_refl. }
    rewrite Hset.
    apply wf_collision.
    - simpl. lia.
    - constructor.
      + exact Hstored.
      + constructor; [exact Hentry|constructor].
    - constructor.
      + intro Hin. apply Hdistinct.
        apply (proj1 (InA_cons (binding_equiv E) (stored, old_value)
          (key, value) [])) in Hin.
        destruct Hin as [Hrelated|Htail]; [exact Hrelated|inversion Htail].
      + constructor; [intro Hin; inversion Hin|constructor].
  Qed.

Lemma set_tree_leaf_distinct_wf :
    forall fuel depth prefix full_hash key stored_hash stored
           (old_value value : A) (eqb : K -> K -> bool),
      depth < branch_levels ->
      length prefix = depth ->
      wf E hash seed depth prefix (Leaf stored_hash stored old_value) ->
      entry_matches hash seed full_hash depth prefix (key, value) ->
      eqb key stored = false ->
      full_hash <> stored_hash ->
      chunk full_hash depth <> chunk stored_hash depth ->
      Equivalence E ->
      (forall first second, E first second -> hash seed first = hash seed second) ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Leaf stored_hash stored old_value)).
  Proof.
    intros fuel depth prefix full_hash key stored_hash stored old_value value eqb
      Hdepth Hlength Hwf Hentry Heqb Hhash Hchunk Hequiv Hcongruent.
    assert (Hnew := wf_leaf_from_entry_descend E (depth := depth)
      (prefix := prefix) (full_hash := full_hash) (key := key) (value := value)
      Hlength Hentry).
    assert (Hold := wf_leaf_descend (depth := depth) (prefix := prefix)
      (full_hash := stored_hash) (key := stored) (value := old_value)
      Hlength Hwf).
    assert (Hhashb : N.eqb full_hash stored_hash = false) by
      (apply N.eqb_neq; exact Hhash).
    destruct fuel as [|fuel]; cbn [set_tree]; rewrite Heqb, Hhashb.
    - eapply wf_join_two_leaf_leaf; eauto.
    - assert (Hchunkb : N.eqb (chunk full_hash depth)
          (chunk stored_hash depth) = false) by
        (apply N.eqb_neq; exact Hchunk).
      cbn [join_worker]. rewrite Hchunkb.
      eapply wf_join_two_leaf_leaf; eauto.
  Qed.

Lemma set_tree_leaf_distinct_root_wf :
    forall full_hash key stored_hash stored (old_value value : A)
           (eqb : K -> K -> bool),
      wf E hash seed 0 [] (Leaf stored_hash stored old_value) ->
      entry_matches hash seed full_hash 0 [] (key, value) ->
      eqb key stored = false ->
      full_hash <> stored_hash ->
      Equivalence E ->
      (forall first second, E first second -> hash seed first = hash seed second) ->
      wf E hash seed 0 []
        (set_tree eqb branch_levels 0 full_hash key value
          (Leaf stored_hash stored old_value)).
  Proof.
    intros full_hash key stored_hash stored old_value value eqb Hstored Hentry
      Heqb Hhash Hequiv Hcongruent.
    destruct Hentry as [Hnew_hash [Hnew_bound Hnew_prefix]].
    assert (Hnew : wf E hash seed 0 [] (Leaf full_hash key value)).
    { apply wf_leaf; [exact Hnew_hash|exact Hnew_bound|exact I]. }
    assert (Hhashb : N.eqb full_hash stored_hash = false) by
      (apply N.eqb_neq; exact Hhash).
    unfold set_tree. cbn. rewrite Heqb, Hhashb.
    eapply wf_join_worker_leaf_leaf_root; eauto.
  Qed.

End LeafUpdateInvariant.

Lemma table_wf_set_singleton_replace :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) key stored (old_value value : A),
    (hash seed stored < hash_space)%N ->
    eqb key stored = true ->
    table_wf E hash (set eqb hash key value
      (singleton eqb hash seed stored old_value)).
Proof.
  intros K Seed A E hash seed eqb key stored old_value value Hbound Hmatch.
  unfold table_wf, singleton, set, empty.
  cbn.
  rewrite Hmatch. apply wf_leaf; [reflexivity|exact Hbound|exact I].
Qed.

Section LeafRemovalInvariant.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

Lemma remove_tree_leaf_wf :
    forall fuel depth prefix full_hash key stored_hash stored (value : A)
           (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Leaf stored_hash stored value) ->
      wf E hash seed depth prefix
        (remove_tree eqb fuel depth full_hash key
          (Leaf stored_hash stored value)).
  Proof.
    intros fuel depth prefix full_hash key stored_hash stored value eqb Hwf.
    destruct fuel; cbn [remove_tree];
      destruct (N.eqb full_hash stored_hash); destruct (eqb key stored);
      eauto using wf_empty.
  Qed.

End LeafRemovalInvariant.

Lemma table_wf_remove_singleton :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) query stored (value : A),
    (hash seed stored < hash_space)%N ->
    table_wf E hash
      (remove eqb hash query (singleton eqb hash seed stored value)).
Proof.
  intros K Seed A E hash seed eqb query stored value Hbound.
  unfold table_wf, singleton, remove, set, empty.
  cbn. destruct (N.eqb (hash seed query) (hash seed stored));
    destruct (eqb query stored).
  - apply wf_empty.
  - apply wf_leaf; [reflexivity|exact Hbound|exact I].
  - apply wf_leaf; [reflexivity|exact Hbound|exact I].
  - apply wf_leaf; [reflexivity|exact Hbound|exact I].
Qed.

Lemma bindings_set_tree_leaf_other_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash stored_hash
         key stored (old value : A) (entry : K * A),
    eqb key stored = false ->
    full_hash <> stored_hash ->
    In entry (bindings (set_tree eqb fuel depth full_hash key value
      (Leaf stored_hash stored old))) <->
    entry = (key, value) \/ entry = (stored, old).
Proof.
  intros K A eqb fuel depth full_hash stored_hash key stored old value entry
    Heqb Hhash.
  apply N.eqb_neq in Hhash.
  destruct fuel; cbn [set_tree]; rewrite Heqb, Hhash;
    rewrite bindings_join_worker; simpl; intuition subst; auto.
Qed.

Lemma remove_tree_leaf_removes :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    eqb key key = true ->
    remove_tree eqb fuel depth full_hash key (Leaf full_hash key value) = Empty.
Proof.
  intros K A eqb fuel depth full_hash key value Heqb.
  destruct fuel; simpl; now rewrite N.eqb_refl, Heqb.
Qed.

Lemma remove_tree_leaf_miss :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key stored
         (value : A),
    eqb key stored = false ->
    remove_tree eqb fuel depth full_hash key (Leaf full_hash stored value) =
    Leaf full_hash stored value.
Proof.
  intros K A eqb fuel depth full_hash key stored value Heqb.
  destruct fuel; cbn [remove_tree]; now rewrite N.eqb_refl, Heqb.
Qed.

Lemma get_tree_leaf_query_equiv :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash stored (value : A) left right,
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E left right ->
    get_tree eqb fuel depth full_hash left (Leaf full_hash stored value) =
    get_tree eqb fuel depth full_hash right (Leaf full_hash stored value).
Proof.
  intros K A E eqb fuel depth full_hash stored value left right
    [Href Hsym Htrans] Heqb Hrelated.
  cbn [get_tree].
  assert (Hsame : eqb left stored = eqb right stored).
  { destruct (eqb left stored) eqn:Hleft;
      destruct (eqb right stored) eqn:Hright; try reflexivity.
    - exfalso.
      apply (proj1 (Heqb left stored)) in Hleft.
      assert (Hright_stored : E right stored).
      { eapply Htrans; [apply Hsym; exact Hrelated|exact Hleft]. }
      apply (proj2 (Heqb right stored)) in Hright_stored.
      rewrite Hright in Hright_stored. exact (diff_false_true Hright_stored).
    - exfalso.
      apply (proj1 (Heqb right stored)) in Hright.
      assert (Hleft_stored : E left stored).
      { eapply Htrans; [exact Hrelated|exact Hright]. }
      apply (proj2 (Heqb left stored)) in Hleft_stored.
      rewrite Hleft in Hleft_stored. exact (diff_false_true Hleft_stored). }
  destruct fuel; cbn [get_tree]; rewrite N.eqb_refl;
    now rewrite Hsame.
Qed.

Lemma get_tree_collision_same_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash query
         (entries : list (K * A)),
    get_tree eqb fuel depth full_hash query (Collision full_hash entries) =
    bucket_get eqb query entries.
Proof. intros. destruct fuel; cbn [get_tree]; now rewrite N.eqb_refl. Qed.

Lemma get_tree_collision_query_equiv :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash left right (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E left right ->
    get_tree eqb fuel depth full_hash left (Collision full_hash entries) =
    get_tree eqb fuel depth full_hash right (Collision full_hash entries).
Proof.
  intros K A E eqb fuel depth full_hash left right entries Hequiv Heqb Hrelated.
  repeat rewrite get_tree_collision_same_hash.
  eapply bucket_get_equiv; eauto.
Qed.

Lemma get_tree_collision_other_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash stored_hash
         (query : K) (entries : list (K * A)),
    full_hash <> stored_hash ->
    get_tree eqb fuel depth full_hash query (Collision stored_hash entries) = None.
Proof.
  intros K A eqb fuel depth full_hash stored_hash query entries Hdifferent.
  apply N.eqb_neq in Hdifferent.
  destruct fuel; cbn [get_tree]; now rewrite Hdifferent.
Qed.

Lemma bindings_normalize_collision :
  forall (K A : Type) full_hash (entries : list (K * A)),
    bindings (normalize_collision full_hash entries) = entries.
Proof.
  intros K A full_hash [|entry [|next tail]];
    cbn [normalize_collision normalize_bucket bindings].
  - reflexivity.
  - destruct entry as [key value]. reflexivity.
  - reflexivity.
Qed.

Lemma set_tree_collision_same_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A) entries,
    set_tree eqb fuel depth full_hash key value (Collision full_hash entries) =
    normalize_collision full_hash (bucket_set eqb key value entries).
Proof.
  intros. destruct fuel; cbn [set_tree]; now rewrite N.eqb_refl.
Qed.

Section CollisionUpdateInvariant.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

Lemma set_tree_collision_same_hash_wf :
    forall fuel depth prefix full_hash key (value : A)
           (entries : list (K * A)) (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Collision full_hash entries) ->
      bucket_get eqb key entries <> None ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Collision full_hash entries)).
  Proof.
    intros fuel depth prefix full_hash key value entries eqb Hwf Hhit.
    inversion Hwf as [| |depth' prefix' full_hash' entries' Hlength Hentries Hnodup|];
      subst.
    rewrite set_tree_collision_same_hash.
    apply wf_normalize_collision.
    - eapply bucket_set_forall_hit; eauto.
      intros stored old_value new_value.
      unfold entry_matches. reflexivity.
    - eapply bucket_set_nodup_hit; eauto.
      + intros stored old_value new_value entry.
        unfold binding_equiv. reflexivity.
      + intros entry stored old_value new_value.
        unfold binding_equiv. reflexivity.
  Qed.

Lemma set_tree_collision_miss_wf :
    forall fuel depth prefix full_hash key (value : A)
           (entries : list (K * A)) (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Collision full_hash entries) ->
      entry_matches hash seed full_hash depth prefix (key, value) ->
      Symmetric E ->
      (forall stored old_value,
          In (stored, old_value) entries -> eqb key stored = false) ->
      ~ InA (binding_equiv E) (key, value) entries ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Collision full_hash entries)).
  Proof.
    intros fuel depth prefix full_hash key value entries eqb Hwf Hentry
      Hsymmetric Hmiss Hfresh.
    inversion Hwf as [| |depth' prefix' full_hash' entries' Hlength Hentries Hnodup|];
      subst.
    rewrite set_tree_collision_same_hash.
    apply wf_normalize_collision.
    - rewrite bucket_set_miss by exact Hmiss.
      apply Forall_app. split; [exact Hentries|].
      constructor; [exact Hentry|constructor].
    - eapply bucket_set_miss_nodup.
      + intros [left_key left_value] [right_key right_value] Hrelated.
        now apply Hsymmetric.
      + exact Hnodup.
      + exact Hmiss.
      + exact Hfresh.
  Qed.

Lemma set_tree_collision_wf :
    forall fuel depth prefix full_hash key (value : A)
           (entries : list (K * A)) (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Collision full_hash entries) ->
      (bucket_get eqb key entries = None ->
        entry_matches hash seed full_hash depth prefix (key, value)) ->
      Symmetric E ->
      (bucket_get eqb key entries = None ->
        ~ InA (binding_equiv E) (key, value) entries) ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Collision full_hash entries)).
  Proof.
    intros fuel depth prefix full_hash key value entries eqb Hwf Hentry
      Hsymmetric Hfresh.
    destruct (bucket_get eqb key entries) eqn:Hget.
    - apply set_tree_collision_same_hash_wf; auto.
      rewrite Hget. discriminate.
    - eapply set_tree_collision_miss_wf; eauto.
      now apply bucket_get_none_miss.
Qed.

Lemma set_tree_collision_distinct_wf :
    forall fuel depth prefix full_hash key stored_hash entries (value : A)
           (eqb : K -> K -> bool),
      depth < branch_levels ->
      length prefix = depth ->
      wf E hash seed depth prefix (Collision stored_hash entries) ->
      entry_matches hash seed full_hash depth prefix (key, value) ->
      full_hash <> stored_hash ->
      chunk full_hash depth <> chunk stored_hash depth ->
      Equivalence E ->
      (forall first second, E first second -> hash seed first = hash seed second) ->
      wf E hash seed depth prefix
        (set_tree eqb fuel depth full_hash key value
          (Collision stored_hash entries)).
  Proof.
    intros fuel depth prefix full_hash key stored_hash entries value eqb Hdepth
      Hlength Hwf Hentry Hhash Hchunk Hequiv Hcongruent.
    assert (Hnew := wf_leaf_from_entry_descend E (depth := depth)
      (prefix := prefix) (full_hash := full_hash) (key := key) (value := value)
      Hlength Hentry).
    assert (Hold := wf_collision_descend (depth := depth) (prefix := prefix)
      (full_hash := stored_hash) (entries := entries) Hlength Hwf).
    assert (Hhashb : N.eqb full_hash stored_hash = false) by
      (apply N.eqb_neq; exact Hhash).
    destruct fuel as [|fuel]; cbn [set_tree]; rewrite Hhashb.
    - eapply wf_join_two_leaf_collision; eauto.
    - assert (Hchunkb : N.eqb (chunk full_hash depth)
          (chunk stored_hash depth) = false) by
        (apply N.eqb_neq; exact Hchunk).
      cbn [join_worker]. rewrite Hchunkb.
      eapply wf_join_two_leaf_collision; eauto.
  Qed.

Lemma set_tree_collision_distinct_root_wf :
    forall full_hash key stored_hash entries (value : A)
           (eqb : K -> K -> bool),
      wf E hash seed 0 [] (Collision stored_hash entries) ->
      entry_matches hash seed full_hash 0 [] (key, value) ->
      full_hash <> stored_hash ->
      Equivalence E ->
      (forall first second, E first second -> hash seed first = hash seed second) ->
      wf E hash seed 0 []
        (set_tree eqb branch_levels 0 full_hash key value
          (Collision stored_hash entries)).
  Proof.
    intros full_hash key stored_hash entries value eqb Hstored Hentry Hhash
      Hequiv Hcongruent.
    destruct Hentry as [Hnew_hash [Hnew_bound Hnew_prefix]].
    assert (Hnew : wf E hash seed 0 [] (Leaf full_hash key value)).
    { apply wf_leaf; [exact Hnew_hash|exact Hnew_bound|exact I]. }
    assert (Hhashb : N.eqb full_hash stored_hash = false) by
      (apply N.eqb_neq; exact Hhash).
    unfold set_tree. cbn. rewrite Hhashb.
    eapply wf_join_worker_leaf_collision_root; eauto.
  Qed.

End CollisionUpdateInvariant.

Lemma get_tree_normalize_collision_same_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash query
         (entries : list (K * A)),
    get_tree eqb fuel depth full_hash query (normalize_collision full_hash entries) =
    bucket_get eqb query entries.
Proof.
  intros K A eqb fuel depth full_hash query entries.
  destruct fuel; destruct entries as [|entry [|next tail]];
    cbn [normalize_collision normalize_bucket get_tree bucket_get].
  all: try reflexivity.
  all: try (destruct entry as [key value]; now rewrite N.eqb_refl).
  all: now rewrite N.eqb_refl.
Qed.

Lemma set_tree_collision_miss_bindings :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A) entries,
    (forall stored old_value, In (stored, old_value) entries -> eqb key stored = false) ->
    bindings (set_tree eqb fuel depth full_hash key value (Collision full_hash entries)) =
    entries ++ [(key, value)].
Proof.
  intros K A eqb fuel depth full_hash key value entries Hmiss.
  rewrite set_tree_collision_same_hash.
  rewrite bindings_normalize_collision.
  now apply bucket_set_miss.
Qed.

Lemma get_tree_collision_after_set :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A) entries,
    (forall query, eqb query query = true) ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value (Collision full_hash entries)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value entries Heqb.
  rewrite set_tree_collision_same_hash.
  rewrite get_tree_normalize_collision_same_hash.
  now apply bucket_get_after_set.
Qed.

Lemma remove_tree_collision_same_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (entries : list (K * A)),
    remove_tree eqb fuel depth full_hash key (Collision full_hash entries) =
    normalize_collision full_hash (bucket_remove eqb key entries).
Proof.
  intros. destruct fuel; cbn [remove_tree]; now rewrite N.eqb_refl.
Qed.

Section CollisionInvariant.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

Lemma remove_tree_collision_same_hash_wf :
    forall fuel depth prefix full_hash key (entries : list (K * A))
           (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Collision full_hash entries) ->
      wf E hash seed depth prefix
        (remove_tree eqb fuel depth full_hash key (Collision full_hash entries)).
  Proof.
    intros fuel depth prefix full_hash key entries eqb Hwf.
    rewrite remove_tree_collision_same_hash.
    now eapply wf_collision_remove.
  Qed.

End CollisionInvariant.

Section CollisionRemovalInvariant.

  Context {K Seed A : Type}.
  Variable E : K -> K -> Prop.
  Variable hash : Seed -> K -> N.
  Variable seed : Seed.

Lemma remove_tree_collision_wf :
    forall fuel depth prefix full_hash key stored_hash
           (entries : list (K * A)) (eqb : K -> K -> bool),
      wf E hash seed depth prefix (Collision stored_hash entries) ->
      wf E hash seed depth prefix
        (remove_tree eqb fuel depth full_hash key
          (Collision stored_hash entries)).
  Proof.
    intros fuel depth prefix full_hash key stored_hash entries eqb Hwf.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    - apply N.eqb_eq in Hhash. subst full_hash.
      now apply remove_tree_collision_same_hash_wf.
    - destruct fuel; cbn [remove_tree]; now rewrite Hhash.
  Qed.

End CollisionRemovalInvariant.

Lemma remove_tree_collision_miss_bindings :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (entries : list (K * A)),
    (forall stored value, In (stored, value) entries -> eqb key stored = false) ->
    bindings (remove_tree eqb fuel depth full_hash key (Collision full_hash entries)) =
    entries.
Proof.
  intros K A eqb fuel depth full_hash key entries Hmiss.
  rewrite remove_tree_collision_same_hash.
  rewrite bindings_normalize_collision.
  now apply bucket_remove_miss.
Qed.

Lemma set_tree_empty_bindings :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    bindings (set_tree eqb fuel depth full_hash key value Empty) = [(key, value)].
Proof. intros. destruct fuel; reflexivity. Qed.

Lemma remove_tree_empty_bindings :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key,
    @bindings K A (remove_tree eqb fuel depth full_hash key Empty) = [].
Proof. intros. destruct fuel; reflexivity. Qed.

Lemma bucket_remove_in :
  forall (K A : Type) (eqb : K -> K -> bool) key
         (entries : list (K * A)) entry,
    In entry (bucket_remove eqb key entries) -> In entry entries.
Proof.
  intros K A eqb key entries.
  induction entries as [|[stored value] tail IH]; intros entry Hin; simpl in *.
  - contradiction.
  - destruct (eqb key stored) eqn:Hstored.
    + now right.
    + destruct Hin as [Hin|Hin].
      * now left.
      * now right; apply IH.
Qed.

Lemma bindings_remove_tree_in :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (t : tree K A) entry,
    In entry (bindings (remove_tree eqb fuel depth full_hash key t)) ->
    In entry (bindings t).
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key t entry Hin;
    destruct t as [|stored_hash stored value|stored_hash entries|bitmap children].
  - cbn [remove_tree] in Hin. contradiction.
  - cbn [remove_tree] in Hin.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + destruct (eqb key stored) eqn:Hkey;
        cbn in Hin |- *;
        try contradiction; exact Hin.
    + cbn in Hin. exact Hin.
  - cbn [remove_tree] in Hin.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash; cbn in Hin |- *.
    + rewrite bindings_normalize_collision in Hin.
      now apply bucket_remove_in in Hin.
    + exact Hin.
  - cbn [remove_tree] in Hin |- *. exact Hin.
  - cbn [remove_tree] in Hin. contradiction.
  - cbn [remove_tree] in Hin.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + destruct (eqb key stored) eqn:Hkey;
        cbn in Hin |- *;
        try contradiction; exact Hin.
    + cbn in Hin. exact Hin.
  - cbn [remove_tree] in Hin.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash; cbn in Hin |- *.
    + rewrite bindings_normalize_collision in Hin.
      now apply bucket_remove_in in Hin.
    + exact Hin.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    2: { rewrite (remove_tree_branch_slot_absent eqb fuel depth full_hash key
      bitmap children Hpresent) in Hin. exact Hin. }
    destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild.
    2: { rewrite (remove_tree_branch_dense_missing eqb fuel depth full_hash key
      bitmap children Hpresent Hchild) in Hin. exact Hin. }
    assert (Hindex : rank bitmap (chunk full_hash depth) < length children).
    { apply (proj1 (nth_error_Some children
        (rank bitmap (chunk full_hash depth)))).
      unfold dense_get in Hchild. rewrite Hchild. discriminate. }
    assert (Hchildin : In child children).
    { apply nth_error_In with (n := rank bitmap (chunk full_hash depth)).
      exact Hchild. }
    rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
      children Hpresent Hchild) in Hin.
    destruct (remove_tree eqb fuel (S depth) full_hash key child)
      as [|child_hash child_key child_value|child_hash child_entries|child_bitmap child_children]
      eqn:Hremove; simpl in Hin.
    + now apply bindings_branch_remove_in in Hin.
    + destruct (bindings_branch_replace_in bitmap (chunk full_hash depth)
        _ children entry Hindex Hin) as [Hnew|Hold].
      * rewrite <- Hremove in Hnew.
        apply IH with (t := child) (depth := S depth)
          (full_hash := full_hash) (key := key) in Hnew.
        apply in_flat_map. now exists child.
      * exact Hold.
    + destruct (bindings_branch_replace_in bitmap (chunk full_hash depth)
        _ children entry Hindex Hin) as [Hnew|Hold].
      * rewrite <- Hremove in Hnew.
        apply IH with (t := child) (depth := S depth)
          (full_hash := full_hash) (key := key) in Hnew.
        apply in_flat_map. now exists child.
      * exact Hold.
    + destruct (bindings_branch_replace_in bitmap (chunk full_hash depth)
        _ children entry Hindex Hin) as [Hnew|Hold].
      * rewrite <- Hremove in Hnew.
        apply IH with (t := child) (depth := S depth)
          (full_hash := full_hash) (key := key) in Hnew.
        apply in_flat_map. now exists child.
      * exact Hold.
Qed.

Lemma bindings_remove_tree_subseq :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (t : tree K A),
    list_subseq (bindings (remove_tree eqb fuel depth full_hash key t))
      (bindings t).
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key t;
    destruct t as [|stored_hash stored value|stored_hash entries|bitmap children].
  - constructor.
  - cbn [remove_tree].
    destruct (N.eqb full_hash stored_hash);
      destruct (eqb key stored); simpl.
    + apply list_subseq_drop. constructor.
    + apply list_subseq_refl.
    + apply list_subseq_refl.
    + apply list_subseq_refl.
  - cbn [remove_tree].
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + rewrite bindings_normalize_collision.
      apply bucket_remove_subseq.
    + apply list_subseq_refl.
  - apply list_subseq_refl.
  - constructor.
  - cbn [remove_tree].
    destruct (N.eqb full_hash stored_hash);
      destruct (eqb key stored); simpl.
    + apply list_subseq_drop. constructor.
    + apply list_subseq_refl.
    + apply list_subseq_refl.
    + apply list_subseq_refl.
  - cbn [remove_tree].
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + rewrite bindings_normalize_collision.
      apply bucket_remove_subseq.
    + apply list_subseq_refl.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    2: { rewrite (remove_tree_branch_slot_absent eqb fuel depth full_hash key
      bitmap children Hpresent). apply list_subseq_refl. }
    destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild.
    2: { rewrite (remove_tree_branch_dense_missing eqb fuel depth full_hash key
      bitmap children Hpresent Hchild). apply list_subseq_refl. }
    rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
      children Hpresent Hchild).
    destruct (remove_tree eqb fuel (S depth) full_hash key child)
      as [|child_hash child_key child_value|child_hash child_entries|child_bitmap child_children]
      eqn:Hremove.
    + unfold branch_remove.
      destruct (dense_remove (rank bitmap (chunk full_hash depth)) children)
        as [|head tail] eqn:Hremaining; simpl.
      * pose proof (@flat_map_dense_remove_subseq K A
          (rank bitmap (chunk full_hash depth)) children) as Hsub.
        rewrite Hremaining in Hsub. exact Hsub.
      * change (list_subseq (flat_map bindings (head :: tail))
          (flat_map bindings children)).
        pose proof (@flat_map_dense_remove_subseq K A
          (rank bitmap (chunk full_hash depth)) children) as Hsub.
        rewrite Hremaining in Hsub. exact Hsub.
    + apply flat_map_dense_replace_subseq with (old := child).
      * exact Hchild.
      * rewrite <- Hremove. apply IH.
    + apply flat_map_dense_replace_subseq with (old := child).
      * exact Hchild.
      * rewrite <- Hremove. apply IH.
    + apply flat_map_dense_replace_subseq with (old := child).
      * exact Hchild.
      * rewrite <- Hremove. apply IH.
Qed.

Lemma bindings_remove_tree_nodup :
  forall (K A : Type) (R : (K * A) -> (K * A) -> Prop)
         (eqb : K -> K -> bool) fuel depth full_hash key (t : tree K A),
    NoDupA R (bindings t) ->
    NoDupA R (bindings (remove_tree eqb fuel depth full_hash key t)).
Proof.
  intros K A R eqb fuel depth full_hash key t Hnodup.
  apply NoDupA_list_subseq with (source := bindings t).
  - apply bindings_remove_tree_subseq.
  - exact Hnodup.
Qed.

Lemma remove_tree_branch_child_wf_nonempty_auto :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (key : K)
         bitmap (children : list (tree K A)) (eqb : K -> K -> bool)
         child child',
    wf E hash seed depth prefix (Branch bitmap children) ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    remove_tree eqb fuel (S depth) full_hash key child = child' ->
    child' <> Empty ->
    wf E hash seed (S depth) (prefix ++ [chunk full_hash depth]) child' ->
    wf E hash seed depth prefix
      (remove_tree eqb (S fuel) depth full_hash key (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed fuel depth prefix full_hash key bitmap children
    eqb child child' Hwf Hpresent Hchild Hremove Hnonempty Hchildwf.
  rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
    children Hpresent Hchild).
  rewrite Hremove.
  destruct child'; try contradiction.
  all: apply wf_branch_replace with (slot := chunk full_hash depth);
    try assumption || apply chunk_bound.
  all: pose proof (@bindings_remove_tree_nodup K A (binding_equiv E) eqb
    (S fuel) depth full_hash key (Branch bitmap children)) as Hnodup.
  all: rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
    children Hpresent Hchild) in Hnodup.
  all: rewrite Hremove in Hnodup.
  all: apply Hnodup.
  all: exact (@wf_bindings_nodup K Seed A E hash seed depth prefix
    (Branch bitmap children) Hwf).
Qed.

Lemma remove_tree_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (t : tree K A),
    wf E hash seed depth prefix t ->
    wf E hash seed depth prefix
      (remove_tree eqb fuel depth full_hash key t).
Proof.
  intros K Seed A E hash seed eqb fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash key t Hwf.
  - destruct t as [|stored_hash stored value|stored_hash entries|bitmap children].
    + apply remove_tree_empty_wf.
    + apply remove_tree_leaf_wf. exact Hwf.
    + apply remove_tree_collision_wf. exact Hwf.
    + exact Hwf.
  - destruct t as [|stored_hash stored value|stored_hash entries|bitmap children].
    + apply remove_tree_empty_wf.
    + apply remove_tree_leaf_wf. exact Hwf.
    + apply remove_tree_collision_wf. exact Hwf.
    + destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
      * destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth)
          Hpresent) as [child [Hchild [Hnonempty Hchildwf]]].
        destruct (remove_tree eqb fuel (S depth) full_hash key child)
          as [|child_hash child_key child_value|child_hash child_entries|child_bitmap child_children]
          eqn:Hremove.
        -- destruct (dense_remove (rank bitmap (chunk full_hash depth)) children)
             as [|head tail] eqn:Hdense.
           ++ rewrite (remove_tree_branch_child eqb fuel depth full_hash key
                bitmap children Hpresent Hchild).
              rewrite Hremove. unfold branch_remove. rewrite Hdense.
              apply wf_empty.
           ++ apply remove_tree_branch_child_wf_removed_nonempty_wf with
                (child := child); try assumption.
              now rewrite Hdense.
        -- apply remove_tree_branch_child_wf_nonempty_auto with
             (child := child) (child' := Leaf child_hash child_key child_value);
             try assumption.
           ++ discriminate.
           ++ rewrite <- Hremove. apply IH. exact Hchildwf.
        -- apply remove_tree_branch_child_wf_nonempty_auto with
             (child := child) (child' := Collision child_hash child_entries);
             try assumption.
           ++ discriminate.
           ++ rewrite <- Hremove. apply IH. exact Hchildwf.
        -- apply remove_tree_branch_child_wf_nonempty_auto with
             (child := child) (child' := Branch child_bitmap child_children);
             try assumption.
           ++ discriminate.
           ++ rewrite <- Hremove. apply IH. exact Hchildwf.
      * apply remove_tree_branch_slot_absent_wf; assumption.
Qed.

Lemma table_wf_remove :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) key (m : table K Seed A),
    @table_wf K Seed A E hash m ->
    @table_wf K Seed A E hash (remove eqb hash key m).
Proof.
  intros K Seed A E hash eqb key [seed root] Hwf.
  change (wf E hash seed 0 [] root) in Hwf.
  change (wf E hash seed 0 []
    (remove_tree eqb branch_levels 0 (hash seed key) key root)).
  apply remove_tree_wf. exact Hwf.
Qed.

Lemma bindings_set_tree_key_origin :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A) (t : tree K A) entry,
    In entry (bindings (set_tree eqb fuel depth full_hash key value t)) ->
    (exists old_value, In (fst entry, old_value) (bindings t)) \/
    fst entry = key.
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key value t entry Hin;
    destruct t as [|stored_hash stored old_value|stored_hash entries|bitmap children].
  - simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
  - cbn [set_tree] in Hin.
    destruct (eqb key stored) eqn:Hkey.
    + destruct Hin as [Hin|[]]. subst entry. left.
      exists old_value. now left.
    + destruct (N.eqb full_hash stored_hash) eqn:Hhash.
      * destruct Hin as [Hin|[Hin|[]]]; subst entry.
        -- left. exists old_value. now left.
        -- now right.
      * rewrite bindings_join_worker in Hin.
        destruct Hin as [Hin|Hin].
        -- simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
        -- simpl in Hin. destruct Hin as [Hin|[]]. subst entry.
           left. exists old_value. now left.
  - cbn [set_tree] in Hin.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + rewrite bindings_normalize_collision in Hin.
      destruct (@bucket_set_key_origin K A eqb key value entries entry Hin)
        as [[prior Hprior]|Hnew].
      * left. exists prior. exact Hprior.
      * now right.
    + rewrite bindings_join_worker in Hin.
      destruct Hin as [Hin|Hin].
      * simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
      * destruct entry as [entry_key entry_value].
        left. exists entry_value. exact Hin.
  - cbn [set_tree] in Hin. destruct entry as [entry_key entry_value].
    left. exists entry_value. exact Hin.
  - simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
  - cbn [set_tree] in Hin.
    destruct (eqb key stored) eqn:Hkey.
    + destruct Hin as [Hin|[]]. subst entry. left.
      exists old_value. now left.
    + destruct (N.eqb full_hash stored_hash) eqn:Hhash.
      * destruct Hin as [Hin|[Hin|[]]]; subst entry.
        -- left. exists old_value. now left.
        -- now right.
      * rewrite bindings_join_worker in Hin.
        destruct Hin as [Hin|Hin].
        -- simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
        -- simpl in Hin. destruct Hin as [Hin|[]]. subst entry.
           left. exists old_value. now left.
  - cbn [set_tree] in Hin.
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + rewrite bindings_normalize_collision in Hin.
      destruct (@bucket_set_key_origin K A eqb key value entries entry Hin)
        as [[prior Hprior]|Hnew].
      * left. exists prior. exact Hprior.
      * now right.
    + rewrite bindings_join_worker in Hin.
      destruct Hin as [Hin|Hin].
      * simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
      * destruct entry as [entry_key entry_value].
        left. exists entry_value. exact Hin.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    + destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
        as [child|] eqn:Hchild.
      * assert (Hindex : rank bitmap (chunk full_hash depth) < length children).
        { apply (proj1 (nth_error_Some children
            (rank bitmap (chunk full_hash depth)))).
          unfold dense_get in Hchild. rewrite Hchild. discriminate. }
        assert (Hchildin : In child children).
        { apply nth_error_In with (n := rank bitmap (chunk full_hash depth)).
          exact Hchild. }
        rewrite (set_tree_branch_child eqb fuel depth full_hash key value bitmap
          children Hpresent Hchild) in Hin.
        destruct (bindings_branch_replace_in bitmap (chunk full_hash depth)
          (set_tree eqb fuel (S depth) full_hash key value child) children entry
          Hindex Hin) as [Hnew|Hold].
        -- destruct (IH (S depth) full_hash key value child entry Hnew)
             as [[prior Hprior]|Hkey].
           ++ left. exists prior. apply in_flat_map.
              now exists child.
           ++ now right.
        -- destruct entry as [entry_key entry_value].
           left. exists entry_value. exact Hold.
      * rewrite (set_tree_branch_dense_missing eqb fuel depth full_hash key value
          bitmap children Hpresent Hchild) in Hin.
        apply bindings_branch_insert in Hin. destruct Hin as [Hin|Hin].
        -- simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
        -- destruct entry as [entry_key entry_value].
           left. exists entry_value. exact Hin.
    + rewrite (set_tree_branch_slot_absent eqb fuel depth full_hash key value
        bitmap children Hpresent) in Hin.
      apply bindings_branch_insert in Hin. destruct Hin as [Hin|Hin].
      * simpl in Hin. destruct Hin as [Hin|[]]. subst entry. now right.
      * destruct entry as [entry_key entry_value].
        left. exists entry_value. exact Hin.
Qed.

Lemma bindings_branch_replace_set_tree_key_origin :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A) bitmap slot children child entry,
    dense_get (rank bitmap slot) children = Some child ->
    In entry (bindings (branch_replace bitmap slot
      (set_tree eqb fuel depth full_hash key value child) children)) ->
    (exists old_value, In (fst entry, old_value)
      (bindings (Branch bitmap children))) \/
    fst entry = key.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap slot children child entry
    Hchild Hin.
  assert (Hindex : rank bitmap slot < length children).
  { apply (proj1 (nth_error_Some children (rank bitmap slot))).
    unfold dense_get in Hchild. rewrite Hchild. discriminate. }
  assert (Hchildin : In child children).
  { apply nth_error_In with (n := rank bitmap slot). exact Hchild. }
  destruct (bindings_branch_replace_in bitmap slot
    (set_tree eqb fuel depth full_hash key value child) children entry Hindex Hin)
    as [Hnew|Hold].
  - destruct (@bindings_set_tree_key_origin K A eqb fuel depth full_hash key value
      child entry Hnew) as [[prior Hprior]|Hkey].
    + left. exists prior. apply in_flat_map. now exists child.
    + now right.
  - destruct entry as [entry_key entry_value].
    left. exists entry_value. exact Hold.
Qed.

Lemma wf_sibling_set_tree_bindings_disjoint :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix selected_slot
         sibling_slot full_hash (key : K) (value : A) child sibling entry,
    Equivalence E ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    length prefix = depth ->
    selected_slot <> sibling_slot ->
    full_hash = hash seed key ->
    chunk full_hash depth = selected_slot ->
    wf E hash seed (S depth) (prefix ++ [selected_slot]) child ->
    wf E hash seed (S depth) (prefix ++ [sibling_slot]) sibling ->
    InA (binding_equiv E) entry
      (bindings (set_tree eqb fuel (S depth) full_hash key value child)) ->
    InA (binding_equiv E) entry (bindings sibling) -> False.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix selected_slot sibling_slot
    full_hash key value child sibling entry Hequiv Hcongruent Hlength Hslots
    Hhash Hroute Hchild Hsibling Hupdated Hsiblingin.
  destruct Hequiv as [Href Hsym Htrans].
  pose proof (Build_Equivalence E Href Hsym Htrans) as Hequiv.
  destruct (inA_witness Hupdated) as [updated [Hupdatedin Hentryupdated]].
  destruct (inA_witness Hsiblingin) as [sibling_entry
    [Hsibling_entry Hentrysibling]].
  destruct (@bindings_set_tree_key_origin K A eqb fuel (S depth) full_hash key
    value child updated Hupdatedin) as [[prior Hprior]|Hnew].
  - eapply (@wf_sibling_bindings_disjoint K Seed A E hash seed depth prefix
      selected_slot sibling_slot child sibling Hequiv Hcongruent Hlength Hslots
      Hchild Hsibling entry).
    + apply (proj2 (InA_alt (binding_equiv E) entry (bindings child))).
      exists (fst updated, prior). split.
      * unfold binding_equiv in Hentryupdated |-.
        exact Hentryupdated.
      * exact Hprior.
    + exact Hsiblingin.
  - apply (@wf_sibling_key_fresh K Seed A E hash seed depth prefix
      selected_slot sibling_slot sibling full_hash key value Hcongruent Hlength
      Hslots Hhash Hroute Hsibling).
    apply (proj2 (InA_alt (binding_equiv E) (key, value) (bindings sibling))).
    exists sibling_entry. split.
    + unfold binding_equiv in Hentryupdated, Hentrysibling |-.
      rewrite <- Hnew.
      eapply Htrans; [|exact Hentrysibling].
      now apply Hsym.
    + exact Hsibling_entry.
Qed.

Lemma wf_set_tree_bindings_disjoint_segments :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix selected_slot
         slots siblings full_hash (key : K) (value : A) child,
    Equivalence E ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    length prefix = depth ->
    full_hash = hash seed key ->
    chunk full_hash depth = selected_slot ->
    wf E hash seed (S depth) (prefix ++ [selected_slot]) child ->
    Forall2 (fun slot sibling => sibling <> Empty /\
      wf E hash seed (S depth) (prefix ++ [slot]) sibling) slots siblings ->
    (forall sibling_slot, In sibling_slot slots -> selected_slot <> sibling_slot) ->
    forall entry,
      InA (binding_equiv E) entry
        (bindings (set_tree eqb fuel (S depth) full_hash key value child)) ->
      InA (binding_equiv E) entry (flat_map bindings siblings) -> False.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix selected_slot slots siblings
    full_hash key value child Hequiv Hcongruent Hlength Hhash Hroute Hchild
    Hsiblings Hdistinct entry Hupdated Hin.
  destruct (inA_witness Hin) as [stored [Hstored Hentrystored]].
  apply in_flat_map in Hstored.
  destruct Hstored as [sibling [Hsiblingin Hstored]].
  destruct (forall2_child_wf_in (depth := depth) prefix Hsiblings sibling Hsiblingin)
    as [sibling_slot [Hslot [Hnonempty Hsibling]]].
  eapply (@wf_sibling_set_tree_bindings_disjoint K Seed A E hash seed eqb fuel
    depth prefix selected_slot sibling_slot full_hash key value child sibling
    entry Hequiv Hcongruent Hlength (Hdistinct sibling_slot Hslot) Hhash Hroute
    Hchild Hsibling Hupdated).
  apply (proj2 (InA_alt (binding_equiv E) entry (bindings sibling))).
  exists stored. split; assumption.
Qed.

Lemma set_tree_branch_child_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) bitmap children child,
    Equivalence E ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    wf E hash seed depth prefix (Branch bitmap children) ->
    length prefix = depth ->
    full_hash = hash seed key ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    NoDupA (binding_equiv E)
      (bindings (set_tree eqb fuel (S depth) full_hash key value child)) ->
    NoDupA (binding_equiv E)
      (bindings (branch_replace bitmap (chunk full_hash depth)
        (set_tree eqb fuel (S depth) full_hash key value child) children)).
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value bitmap
    children child Hequiv Hcongruent Hwf Hlength Hhash Hpresent Hchild Hupdated.
  inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hchildren_length
    Hchildren Horiginal].
  assert (Hnth : nth_error (occupied_slots bitmap)
    (rank bitmap (chunk full_hash depth)) = Some (chunk full_hash depth)).
  { destruct (@occupied_slots_rank_split_N (chunk full_hash depth) bitmap
      (chunk_bound full_hash depth) Hpresent) as [before [after [Hslots Hrank]]].
    rewrite Hslots, <- Hrank.
    rewrite nth_error_app2 by lia.
    replace (length before - length before) with 0 by lia.
    reflexivity. }
  destruct (@Forall2_dense_get_split N (tree K A)
    (fun slot sibling => sibling <> Empty /\
      wf E hash seed (S depth) (prefix ++ [slot]) sibling)
    (rank bitmap (chunk full_hash depth)) (occupied_slots bitmap) children
    (chunk full_hash depth) child Hchildren Hnth Hchild)
    as [slots_before [slots_after [children_before [children_after
      [Hslots [Hchildren_split [Hslots_length
        [Hbefore [Hchildwf Hafter]]]]]]]]].
  destruct Hchildwf as [Hchild_nonempty Hchildwf].
  assert (Hslots_nodup : NoDup (occupied_slots bitmap)).
  { apply occupied_slots_nodup. }
  assert (Hbefore_slots : forall sibling_slot,
    In sibling_slot slots_before -> chunk full_hash depth <> sibling_slot).
  { intros sibling_slot Hin.
    apply (@NoDup_before_selected N slots_before slots_after
      (chunk full_hash depth) sibling_slot).
    - rewrite <- Hslots. exact Hslots_nodup.
    - exact Hin. }
  assert (Hafter_slots : forall sibling_slot,
    In sibling_slot slots_after -> chunk full_hash depth <> sibling_slot).
  { intros sibling_slot Hin.
    apply (@NoDup_after_selected N slots_before slots_after
      (chunk full_hash depth) sibling_slot).
    - rewrite <- Hslots. exact Hslots_nodup.
    - exact Hin. }
  assert (Hbefore_cross : forall entry,
    InA (binding_equiv E) entry (flat_map bindings children_before) ->
    InA (binding_equiv E) entry
      (bindings (set_tree eqb fuel (S depth) full_hash key value child)) -> False).
  { intros entry Hinbefore Hinupdated.
    eapply (@wf_set_tree_bindings_disjoint_segments K Seed A E hash seed eqb
      fuel depth prefix (chunk full_hash depth) slots_before children_before
      full_hash key value child); eauto. }
  assert (Hafter_cross : forall entry,
    InA (binding_equiv E) entry
      (bindings (set_tree eqb fuel (S depth) full_hash key value child)) ->
    InA (binding_equiv E) entry (flat_map bindings children_after) -> False).
  { eapply (@wf_set_tree_bindings_disjoint_segments K Seed A E hash seed eqb
      fuel depth prefix (chunk full_hash depth) slots_after children_after
      full_hash key value child); eauto. }
  assert (Hbefore_length : length children_before =
    rank bitmap (chunk full_hash depth)).
  { pose proof (Forall2_length Hbefore) as Hlength'. rewrite Hslots_length in Hlength'.
    symmetry. exact Hlength'. }
  assert (Hreplace : dense_replace (rank bitmap (chunk full_hash depth))
    (set_tree eqb fuel (S depth) full_hash key value child) children =
    children_before ++
      set_tree eqb fuel (S depth) full_hash key value child :: children_after).
  { rewrite Hchildren_split.
    apply dense_replace_at_split. exact Hbefore_length. }
  simpl in Horiginal |-.
  rewrite Hchildren_split in Horiginal.
  repeat rewrite flat_map_app in Horiginal.
  simpl in Horiginal.
  unfold branch_replace. simpl. rewrite Hreplace.
  repeat rewrite flat_map_app. simpl.
  apply (@NoDupA_replace_between (K * A) (binding_equiv E)
    (flat_map bindings children_before) (bindings child)
    (bindings (set_tree eqb fuel (S depth) full_hash key value child))
    (flat_map bindings children_after)).
  - now apply binding_equiv_equiv.
  - exact Horiginal.
  - exact Hupdated.
  - exact Hbefore_cross.
  - exact Hafter_cross.
Qed.

Lemma set_tree_branch_child_wf_fresh :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) bitmap children child updated_child,
    Equivalence E ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    wf E hash seed depth prefix (Branch bitmap children) ->
    length prefix = depth ->
    full_hash = hash seed key ->
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    set_tree eqb fuel (S depth) full_hash key value child = updated_child ->
    updated_child <> Empty ->
    wf E hash seed (S depth) (prefix ++ [chunk full_hash depth]) updated_child ->
    wf E hash seed depth prefix
      (set_tree eqb (S fuel) depth full_hash key value (Branch bitmap children)).
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value bitmap
    children child updated_child Hequiv Hcongruent Hwf Hlength Hhash Hpresent
    Hchild Hset Hnonempty Hupdatedwf.
  eapply (@set_tree_branch_child_wf_nonempty K Seed A E hash seed fuel depth
    prefix full_hash key value bitmap children eqb child updated_child).
  - exact Hwf.
  - exact Hpresent.
  - exact Hchild.
  - exact Hset.
  - exact Hnonempty.
  - exact Hupdatedwf.
  - rewrite <- Hset.
    eapply (@set_tree_branch_child_nodup K Seed A E hash seed eqb fuel depth
      prefix full_hash key value bitmap children child).
    + exact Hequiv.
    + exact Hcongruent.
    + exact Hwf.
    + exact Hlength.
    + exact Hhash.
    + exact Hpresent.
    + exact Hchild.
    + rewrite Hset.
      apply (@wf_bindings_nodup K Seed A E hash seed (S depth)
        (prefix ++ [chunk full_hash depth]) updated_child Hupdatedwf).
Qed.

Lemma elements_remove_in :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (m : table K Seed A) entry,
    In entry (elements (remove eqb hash key m)) ->
    In entry (elements m).
Proof.
  intros K Seed A eqb hash key [seed root] entry Hin.
  change (In entry
    (bindings (remove_tree eqb branch_levels 0 (hash seed key) key root))) in Hin.
  change (In entry (bindings root)).
  now apply bindings_remove_tree_in in Hin.
Qed.

Lemma elements_remove_subseq :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (m : table K Seed A),
    list_subseq (elements (remove eqb hash key m)) (elements m).
Proof.
  intros K Seed A eqb hash key [seed root].
  change (list_subseq
    (bindings (remove_tree eqb branch_levels 0 (hash seed key) key root))
    (bindings root)).
  apply bindings_remove_tree_subseq.
Qed.

Lemma elements_remove_length_le :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (m : table K Seed A),
    length (elements (remove eqb hash key m)) <= length (elements m).
Proof.
  intros K Seed A eqb hash key m.
  apply list_subseq_length_le. apply elements_remove_subseq.
Qed.

Lemma elements_remove_nodup :
  forall (K Seed A : Type) (R : (K * A) -> (K * A) -> Prop)
         (eqb : K -> K -> bool) (hash : Seed -> K -> N) key
         (m : table K Seed A),
    NoDupA R (elements m) ->
    NoDupA R (elements (remove eqb hash key m)).
Proof.
  intros K Seed A R eqb hash key [seed root] Hnodup.
  change (NoDupA R (bindings root)) in Hnodup.
  change (NoDupA R
    (bindings (remove_tree eqb branch_levels 0 (hash seed key) key root))).
  now apply bindings_remove_tree_nodup.
Qed.

Lemma elements_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (m : table K Seed A),
    table_wf E hash m ->
    NoDupA (binding_equiv E) (elements m).
Proof.
  intros K Seed A E hash [seed root] Hwf.
  change (NoDupA (binding_equiv E) (bindings root)).
  now apply (@wf_bindings_nodup K Seed A E hash seed 0 [] root Hwf).
Qed.

Lemma NoDupA_fst :
  forall (K A : Type) (E : K -> K -> Prop) (entries : list (K * A)),
    NoDupA (fun left right : K * A => E (fst left) (fst right)) entries ->
    NoDupA E (map fst entries).
Proof.
  intros K A E entries Hnodup.
  induction entries as [|[key value] tail IH].
  - constructor.
  - inversion Hnodup as [|head entries Hnotin Htail]; subst.
    simpl. constructor.
    + intro Hin. apply Hnotin.
      apply (proj2 (InA_alt _ (key, value) tail)).
      apply (proj1 (InA_alt E key (map fst tail))) in Hin.
      destruct Hin as [other_key [Hrelated Hin]].
      apply in_map_iff in Hin.
      destruct Hin as [[stored_key stored_value] [Hkey Hin]].
      simpl in Hkey.
      subst stored_key. exists (other_key, stored_value).
      split; assumption.
    + apply IH. exact Htail.
Qed.

Lemma elements_keys_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (m : table K Seed A),
    table_wf E hash m ->
    NoDupA E (map fst (elements m)).
Proof.
  intros K Seed A E hash m Hwf.
  apply NoDupA_fst. now apply (@elements_nodup K Seed A E hash m Hwf).
Qed.

Lemma is_empty_get_none :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (m : table K Seed A),
    is_empty m = true ->
    forall query, get eqb hash query m = None.
Proof.
  intros K Seed A eqb hash [seed root] Hempty query.
  apply is_empty_root_iff in Hempty. subst root. reflexivity.
Qed.

Lemma is_empty_iff_get_none :
  forall (K Seed A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         (hash : Seed -> K -> N) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    table_wf E hash m ->
    (is_empty m = true <-> forall query, get eqb hash query m = None).
Proof.
  intros K Seed A E eqb hash [seed root] Hequiv Heqb Hcongruent Hwf.
  pose proof Hequiv as [Href Hsym Htrans].
  split.
  - apply is_empty_get_none.
  - intro Hall.
    destruct root as [|stored_hash stored value|stored_hash entries|bitmap children].
    + reflexivity.
    + exfalso.
      destruct (@wf_nonempty_has_binding K Seed A E hash seed
        (Leaf stored_hash stored value) 0 [] Hwf) as [entry Hin].
      { discriminate. }
      destruct entry as [entry_key entry_value].
      destruct (@wf_binding_hash K Seed A E hash seed
        (Leaf stored_hash stored value) 0 [] Hwf (entry_key, entry_value) Hin)
        as [full_hash [Hhash Hbound]].
      simpl in Hhash.
      assert (Hget : get eqb hash entry_key
        {| table_seed := seed; table_root := Leaf stored_hash stored value |} =
        Some entry_value).
      { assert (Hkeybound : (hash seed entry_key < hash_space)%N).
        { rewrite <- Hhash. exact Hbound. }
        exact (@get_binding_complete K Seed A E hash eqb entry_key entry_key
          entry_value {| table_seed := seed; table_root := Leaf stored_hash stored value |}
          Hequiv Heqb Hcongruent Hkeybound Hwf Hin (Href entry_key)). }
      rewrite (Hall entry_key) in Hget. discriminate.
    + exfalso.
      destruct (@wf_nonempty_has_binding K Seed A E hash seed
        (Collision stored_hash entries) 0 [] Hwf) as [entry Hin].
      { discriminate. }
      destruct entry as [entry_key entry_value].
      destruct (@wf_binding_hash K Seed A E hash seed
        (Collision stored_hash entries) 0 [] Hwf (entry_key, entry_value) Hin)
        as [full_hash [Hhash Hbound]].
      simpl in Hhash.
      assert (Hget : get eqb hash entry_key
        {| table_seed := seed; table_root := Collision stored_hash entries |} =
        Some entry_value).
      { assert (Hkeybound : (hash seed entry_key < hash_space)%N).
        { rewrite <- Hhash. exact Hbound. }
        exact (@get_binding_complete K Seed A E hash eqb entry_key entry_key
          entry_value {| table_seed := seed; table_root := Collision stored_hash entries |}
          Hequiv Heqb Hcongruent Hkeybound Hwf Hin (Href entry_key)). }
      rewrite (Hall entry_key) in Hget. discriminate.
    + exfalso.
      destruct (@wf_nonempty_has_binding K Seed A E hash seed
        (Branch bitmap children) 0 [] Hwf) as [entry Hin].
      { discriminate. }
      destruct entry as [entry_key entry_value].
      destruct (@wf_binding_hash K Seed A E hash seed
        (Branch bitmap children) 0 [] Hwf (entry_key, entry_value) Hin)
        as [full_hash [Hhash Hbound]].
      simpl in Hhash.
      assert (Hget : get eqb hash entry_key
        {| table_seed := seed; table_root := Branch bitmap children |} =
        Some entry_value).
      { assert (Hkeybound : (hash seed entry_key < hash_space)%N).
        { rewrite <- Hhash. exact Hbound. }
        exact (@get_binding_complete K Seed A E hash eqb entry_key entry_key
          entry_value {| table_seed := seed; table_root := Branch bitmap children |}
          Hequiv Heqb Hcongruent Hkeybound Hwf Hin (Href entry_key)). }
      rewrite (Hall entry_key) in Hget. discriminate.
Qed.

Definition table_extensional {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (left right : table K Seed A) : Prop :=
  forall query, get eqb hash query left = get eqb hash query right.

Lemma table_extensional_equivalence :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    Equivalence (@table_extensional K Seed A eqb hash).
Proof.
  intros K Seed A eqb hash. split.
  - intro table. intro query. reflexivity.
  - intros left right Hext query. symmetry. apply Hext.
  - intros left middle right Hleft Hright query.
    now rewrite Hleft, Hright.
Qed.

Lemma get_tree_query_equiv :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash (left right : K) (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E left right ->
    get_tree eqb fuel depth full_hash left t =
    get_tree eqb fuel depth full_hash right t.
Proof.
  intros K A E eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash left right t
    Hequiv Heqb Hrelated; destruct t as
    [|stored_hash stored value|stored_hash entries|bitmap children].
  - reflexivity.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + apply N.eqb_eq in Hhash. subst stored_hash.
      exact (@get_tree_leaf_query_equiv K A E eqb _ depth full_hash stored
        value left right Hequiv Heqb Hrelated).
    + cbn [get_tree]. now rewrite Hhash.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + apply N.eqb_eq in Hhash. subst stored_hash.
      exact (@get_tree_collision_query_equiv K A E eqb _ depth full_hash
        left right entries Hequiv Heqb Hrelated).
    + cbn [get_tree]. now rewrite Hhash.
  - reflexivity.
  - reflexivity.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + apply N.eqb_eq in Hhash. subst stored_hash.
      exact (@get_tree_leaf_query_equiv K A E eqb _ depth full_hash stored
        value left right Hequiv Heqb Hrelated).
    + cbn [get_tree]. now rewrite Hhash.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + apply N.eqb_eq in Hhash. subst stored_hash.
      exact (@get_tree_collision_query_equiv K A E eqb _ depth full_hash
        left right entries Hequiv Heqb Hrelated).
    + cbn [get_tree]. now rewrite Hhash.
  - cbn [get_tree].
    destruct (bitmap_has bitmap (chunk full_hash depth));
      [destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
       as [child|]; [apply IH|reflexivity]|reflexivity]; assumption.
Qed.

Lemma get_query_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         (hash : Seed -> K -> N) (left right : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E left right ->
    get eqb hash left m = get eqb hash right m.
Proof.
  intros K Seed A E eqb hash left right [seed root]
    Hequiv Heqb Hhash Hrelated.
  change (get_tree eqb branch_levels 0 (hash seed left) left root =
    get_tree eqb branch_levels 0 (hash seed right) right root).
  rewrite (Hhash seed left right Hrelated).
  exact (@get_tree_query_equiv K A E eqb branch_levels 0 (hash seed right)
    left right root Hequiv Heqb Hrelated).
Qed.

Lemma mem_query_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         (hash : Seed -> K -> N) (left right : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E left right ->
    mem eqb hash left m = mem eqb hash right m.
Proof.
  intros K Seed A E eqb hash left right m Hequiv Heqb Hhash Hrelated.
  unfold mem.
  rewrite (@get_query_equiv K Seed A E eqb hash left right m
    Hequiv Heqb Hhash Hrelated).
  reflexivity.
Qed.

Lemma eqb_equiv_same_right :
  forall (K : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         left right stored,
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E left right ->
    eqb left stored = eqb right stored.
Proof.
  intros K E eqb left right stored [Href Hsym Htrans] Heqb Hrelated.
  destruct (eqb left stored) eqn:Hleft;
    destruct (eqb right stored) eqn:Hright; try reflexivity.
  - exfalso. apply (proj1 (Heqb left stored)) in Hleft.
    assert (Hright_stored : E right stored).
    { eapply Htrans; [apply Hsym; exact Hrelated|exact Hleft]. }
    apply (proj2 (Heqb right stored)) in Hright_stored.
    rewrite Hright in Hright_stored. discriminate.
  - exfalso. apply (proj1 (Heqb right stored)) in Hright.
    assert (Hleft_stored : E left stored).
    { eapply Htrans; [exact Hrelated|exact Hright]. }
    apply (proj2 (Heqb left stored)) in Hleft_stored.
    rewrite Hleft in Hleft_stored. discriminate.
Qed.

Lemma eqb_false_of_not_equiv :
  forall (K : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool) left right,
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E left right ->
    eqb left right = false.
Proof.
  intros K E eqb left right Heqb Hdifferent.
  destruct (eqb left right) eqn:Hequal; auto.
  exfalso. apply Hdifferent. now apply (proj1 (Heqb left right)).
Qed.

Lemma bucket_remove_query_equiv :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         left right (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E left right ->
    bucket_remove eqb left entries = bucket_remove eqb right entries.
Proof.
  intros K A E eqb left right entries Hequiv Heqb Hrelated.
  induction entries as [|[stored value] tail IH]; simpl.
  - reflexivity.
  - rewrite (@eqb_equiv_same_right K E eqb left right stored
      Hequiv Heqb Hrelated).
    destruct (eqb right stored); simpl.
    + reflexivity.
    + now rewrite IH.
Qed.

Lemma remove_tree_query_equiv :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash (left right : K) (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E left right ->
    remove_tree eqb fuel depth full_hash left t =
    remove_tree eqb fuel depth full_hash right t.
Proof.
  intros K A E eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash left right t
    Hequiv Heqb Hrelated; destruct t as
    [|stored_hash stored value|stored_hash entries|bitmap children].
  - reflexivity.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash; cbn [remove_tree].
    + rewrite (@eqb_equiv_same_right K E eqb left right stored
        Hequiv Heqb Hrelated). reflexivity.
    + now rewrite Hhash.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash; cbn [remove_tree].
    + rewrite Hhash.
      now rewrite (@bucket_remove_query_equiv K A E eqb left right entries
        Hequiv Heqb Hrelated).
    + now rewrite Hhash.
  - reflexivity.
  - reflexivity.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash; cbn [remove_tree].
    + rewrite (@eqb_equiv_same_right K E eqb left right stored
        Hequiv Heqb Hrelated). reflexivity.
    + now rewrite Hhash.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash; cbn [remove_tree].
    + rewrite Hhash.
      now rewrite (@bucket_remove_query_equiv K A E eqb left right entries
        Hequiv Heqb Hrelated).
    + now rewrite Hhash.
  - cbn [remove_tree].
    destruct (bitmap_has bitmap (chunk full_hash depth));
      [destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
       as [child|]
       ; [rewrite (@IH (S depth) full_hash left right child Hequiv Heqb Hrelated);
          reflexivity|reflexivity]|reflexivity].
Qed.

Lemma table_root_eq :
  forall (K Seed A : Type) (seed : Seed) (left right : tree K A),
    left = right ->
    {| table_seed := seed; table_root := left |} =
    {| table_seed := seed; table_root := right |}.
Proof. intros K Seed A seed left right Hroot. now subst right. Qed.

Lemma remove_query_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         (hash : Seed -> K -> N) (left right : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E left right ->
    remove eqb hash left m = remove eqb hash right m.
Proof.
  intros K Seed A E eqb hash left right [seed root]
    Hequiv Heqb Hhash Hrelated.
  unfold remove.
  apply table_root_eq.
  change (remove_tree eqb branch_levels 0 (hash seed left) left root =
    remove_tree eqb branch_levels 0 (hash seed right) right root).
  rewrite (Hhash seed left right Hrelated).
  apply (@remove_tree_query_equiv K A E eqb branch_levels 0
    (hash seed right) left right root Hequiv Heqb Hrelated).
Qed.

Lemma bucket_remove_head_miss :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         key stored (value : A) tail,
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    E key stored ->
    NoDupA (binding_equiv E) ((stored, value) :: tail) ->
    forall stored' value', In (stored', value') tail ->
      eqb key stored' = false.
Proof.
  intros K A E eqb key stored value tail [Href Hsym Htrans] Heqb
    Hkey_stored Hnodup stored' value' Hin.
  destruct (eqb key stored') eqn:Hkey_stored'.
  - exfalso.
    inversion Hnodup as [|head entries Hnot Htail]; subst.
    apply Hnot.
    apply (proj2 (InA_alt (binding_equiv E) (stored, value) tail)).
    exists (stored', value'). split.
    + unfold binding_equiv.
      eapply Htrans; [apply Hsym; exact Hkey_stored|].
      now apply (proj1 (Heqb key stored')).
    + exact Hin.
  - reflexivity.
Qed.

Lemma bucket_get_after_remove_self :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         key (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    NoDupA (binding_equiv E) entries ->
    bucket_get eqb key (bucket_remove eqb key entries) = None.
Proof.
  intros K A E eqb key entries Hequiv Heqb Hnodup.
  induction entries as [|[stored value] tail IH]; simpl.
  - reflexivity.
  - inversion Hnodup as [|head entries Hnot Htail]; subst.
    destruct (eqb key stored) eqn:Hkey_stored.
    + apply bucket_get_miss.
      intros stored' value' Hin.
      assert (Hfull : NoDupA (binding_equiv E) ((stored, value) :: tail)).
      { constructor; assumption. }
      exact (@bucket_remove_head_miss K A E eqb key stored value tail
        Hequiv Heqb (proj1 (Heqb key stored) Hkey_stored)
        Hfull stored' value' Hin).
    + cbn [bucket_get]. rewrite Hkey_stored.
      apply IH. exact Htail.
Qed.

Lemma get_tree_after_remove_collision_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    wf E hash seed depth prefix (Collision full_hash entries) ->
    get_tree eqb fuel depth full_hash key
      (remove_tree eqb fuel depth full_hash key
        (Collision full_hash entries)) = None.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key entries
    Hequiv Heqb Hwf.
  inversion Hwf as [| |d p h es Hlength Hall Hnodup|]; subst.
  rewrite remove_tree_collision_same_hash.
  rewrite get_tree_normalize_collision_same_hash.
  now apply (@bucket_get_after_remove_self K A E eqb key entries).
Qed.

Lemma get_tree_after_remove_leaf_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    eqb key key = true ->
    get_tree eqb fuel depth full_hash key
      (remove_tree eqb fuel depth full_hash key
        (Leaf full_hash key value)) = None.
Proof.
  intros K A eqb fuel depth full_hash key value Heqb.
  rewrite (remove_tree_leaf_removes eqb fuel depth full_hash key value Heqb).
  apply get_tree_empty.
Qed.

Lemma get_tree_after_remove_leaf_miss :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash stored_hash
         key stored (value : A),
    eqb key stored = false ->
    get_tree eqb fuel depth full_hash key
      (remove_tree eqb fuel depth full_hash key
        (Leaf stored_hash stored value)) = None.
Proof.
  intros K A eqb fuel depth full_hash stored_hash key stored value Hmiss.
  destruct (N.eqb full_hash stored_hash) eqn:Hhash.
  - apply N.eqb_eq in Hhash. subst stored_hash.
    rewrite (remove_tree_leaf_miss eqb fuel depth full_hash key stored value
      Hmiss).
    apply get_tree_leaf_other_key. exact Hmiss.
  - assert (Hremove :
        remove_tree eqb fuel depth full_hash key
          (Leaf stored_hash stored value) = Leaf stored_hash stored value).
    { destruct fuel; cbn [remove_tree]; now rewrite Hhash. }
    rewrite Hremove.
    apply get_tree_leaf_other_hash.
    now apply N.eqb_neq.
Qed.

Lemma get_tree_branch_remove_slot_none :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    get_tree eqb (S fuel) depth full_hash key
      (branch_remove bitmap (chunk full_hash depth) children) = None.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children.
  unfold branch_remove.
  destruct (dense_remove (rank bitmap (chunk full_hash depth)) children)
    as [|child remaining]; simpl.
  - reflexivity.
  - apply get_tree_branch_slot_absent.
    apply bitmap_has_ldiff_bit.
Qed.

Lemma get_tree_branch_replace_same :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         bitmap (children : list (tree K A)) old child,
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some old ->
    get_tree eqb (S fuel) depth full_hash key
      (branch_replace bitmap (chunk full_hash depth) child children) =
    get_tree eqb fuel (S depth) full_hash key child.
Proof.
  intros K A eqb fuel depth full_hash key bitmap children old child
    Hpresent Hget.
  assert (Hindex : rank bitmap (chunk full_hash depth) < length children).
  { apply (proj1 (nth_error_Some children
      (rank bitmap (chunk full_hash depth)))).
    unfold dense_get in Hget. rewrite Hget. discriminate. }
  unfold branch_replace. cbn [get_tree]. rewrite Hpresent.
  rewrite (@dense_get_replace_same (tree K A)
    (rank bitmap (chunk full_hash depth)) child children Hindex).
  reflexivity.
Qed.

Lemma get_tree_branch_insert_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)),
    eqb key key = true ->
    rank bitmap (chunk full_hash depth) <= length children ->
    get_tree eqb (S fuel) depth full_hash key
      (branch_insert bitmap (chunk full_hash depth)
        (Leaf full_hash key value) children) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap children
    Heqb Hindex.
  unfold branch_insert. cbn [get_tree].
  assert (Hpresent : bitmap_has
      (N.lor bitmap (bitmap_bit (chunk full_hash depth)))
      (chunk full_hash depth) = true).
  { apply bitmap_has_lor_right. apply bitmap_bit_has_slot. }
  rewrite Hpresent.
  assert (Hrank : rank (N.lor bitmap (bitmap_bit (chunk full_hash depth)))
      (chunk full_hash depth) = rank bitmap (chunk full_hash depth)).
  { apply rank_lor_bit. apply chunk_bound. }
  rewrite Hrank.
  rewrite (@dense_get_insert_same (tree K A)
    (rank bitmap (chunk full_hash depth))
    (Leaf full_hash key value) children Hindex).
  now apply get_tree_leaf_same.
Qed.

Lemma get_tree_after_set_branch_slot_absent_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)),
    eqb key key = true ->
    bitmap_has bitmap (chunk full_hash depth) = false ->
    rank bitmap (chunk full_hash depth) <= length children ->
    get_tree eqb (S fuel) depth full_hash key
      (set_tree eqb (S fuel) depth full_hash key value
        (Branch bitmap children)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap children
    Heqb Habsent Hindex.
  rewrite (set_tree_branch_slot_absent eqb fuel depth full_hash key value
    bitmap children Habsent).
  now apply get_tree_branch_insert_self.
Qed.

Lemma get_tree_after_set_branch_slot_absent_self_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) bitmap (children : list (tree K A)),
    wf E hash seed depth prefix (Branch bitmap children) ->
    eqb key key = true ->
    bitmap_has bitmap (chunk full_hash depth) = false ->
    get_tree eqb (S fuel) depth full_hash key
      (set_tree eqb (S fuel) depth full_hash key value
        (Branch bitmap children)) = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value
    bitmap children Hwf Heqb Habsent.
  apply get_tree_after_set_branch_slot_absent_self; try assumption.
  inversion Hwf as [| | |d p b cs Hdepth Hbound Hnonzero Hlength
    Hchildren Hnodup]; subst.
  rewrite Hlength. apply rank_le_popcount32.
Qed.

Lemma get_tree_after_set_branch_child_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) bitmap (children : list (tree K A)) child,
    bitmap_has bitmap (chunk full_hash depth) = true ->
    dense_get (rank bitmap (chunk full_hash depth)) children = Some child ->
    get_tree eqb fuel (S depth) full_hash key
      (set_tree eqb fuel (S depth) full_hash key value child) = Some value ->
    get_tree eqb (S fuel) depth full_hash key
      (set_tree eqb (S fuel) depth full_hash key value
        (Branch bitmap children)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value bitmap children child
    Hpresent Hchild Hrecursive.
  rewrite (set_tree_branch_child eqb fuel depth full_hash key value bitmap
    children Hpresent Hchild).
  rewrite (@get_tree_branch_replace_same K A eqb fuel depth full_hash key
    bitmap children child
    (set_tree eqb fuel (S depth) full_hash key value child)
    Hpresent Hchild).
  exact Hrecursive.
Qed.

Lemma get_tree_join_two_right_leaf :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth left_hash right_hash
         (left : tree K A) (key : K) (value : A),
    eqb key key = true ->
    chunk left_hash depth <> chunk right_hash depth ->
    get_tree eqb (S fuel) depth right_hash key
      (join_two left_hash left right_hash (Leaf right_hash key value) depth) =
    Some value.
Proof.
  intros K A eqb fuel depth left_hash right_hash left key value Heqb Hdifferent.
  unfold join_two.
  destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hleft.
  - cbn [get_tree].
    assert (Hpresent : bitmap_has
        (N.lor (bitmap_bit (chunk left_hash depth))
          (bitmap_bit (chunk right_hash depth)))
        (chunk right_hash depth) = true).
    { apply bitmap_has_lor_right. apply bitmap_bit_has_slot. }
    rewrite Hpresent.
    rewrite (@rank_lor_bitmap_bits_lt_right
      (chunk left_hash depth) (chunk right_hash depth)
      (chunk_bound left_hash depth) (chunk_bound right_hash depth) Hleft).
    cbn [dense_get]. now apply get_tree_leaf_same.
  - assert (Hright : N.ltb (chunk right_hash depth) (chunk left_hash depth) = true).
    { apply N.ltb_lt. apply N.ltb_ge in Hleft.
      destruct (N.eq_dec (chunk right_hash depth) (chunk left_hash depth))
        as [Hequal|Hunequal].
      - exfalso. apply Hdifferent. now symmetry.
      - lia. }
    cbn [get_tree].
    assert (Hpresent : bitmap_has
        (N.lor (bitmap_bit (chunk left_hash depth))
          (bitmap_bit (chunk right_hash depth)))
        (chunk right_hash depth) = true).
    { apply bitmap_has_lor_right. apply bitmap_bit_has_slot. }
    rewrite Hpresent.
    rewrite (N.lor_comm (bitmap_bit (chunk left_hash depth))
      (bitmap_bit (chunk right_hash depth))).
    rewrite (@rank_lor_bitmap_bits_lt_left
      (chunk right_hash depth) (chunk left_hash depth)
      (chunk_bound right_hash depth) (chunk_bound left_hash depth) Hright).
    cbn [dense_get]. now apply get_tree_leaf_same.
Qed.

Lemma get_tree_join_worker_right_leaf :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth left_hash right_hash
         (left : tree K A) (key : K) (value : A),
    eqb key key = true ->
    join_falls_back fuel depth left_hash right_hash = false ->
    get_tree eqb fuel depth right_hash key
      (join_worker fuel depth left_hash left right_hash
        (Leaf right_hash key value)) = Some value.
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth left_hash right_hash left key value
    Heqb Hfallback.
  - discriminate Hfallback.
  - cbn [join_worker join_falls_back] in Hfallback |-.
    destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth))
      eqn:Hchunks.
    + assert (Hsame : chunk left_hash depth = chunk right_hash depth).
      { now apply N.eqb_eq. }
      cbn [join_worker]. rewrite Hchunks.
      cbn [get_tree]. rewrite <- Hsame.
      rewrite child_bit_has_slot, child_bit_rank_self.
      cbn [dense_get].
      apply IH. exact Heqb. exact Hfallback.
    + cbn [join_worker]. rewrite Hchunks.
      apply get_tree_join_two_right_leaf; [exact Heqb|].
      now apply N.eqb_neq.
Qed.

Lemma get_tree_join_two_left_leaf :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth left_hash right_hash
         (right : tree K A) (key : K) (value : A),
    eqb key key = true ->
    chunk left_hash depth <> chunk right_hash depth ->
    get_tree eqb (S fuel) depth left_hash key
      (join_two left_hash (Leaf left_hash key value) right_hash right depth) =
    Some value.
Proof.
  intros K A eqb fuel depth left_hash right_hash right key value Heqb Hdifferent.
  unfold join_two.
  destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hleft.
  - cbn [get_tree].
    assert (Hpresent : bitmap_has
        (N.lor (bitmap_bit (chunk left_hash depth))
          (bitmap_bit (chunk right_hash depth)))
        (chunk left_hash depth) = true).
    { apply bitmap_has_lor_left. apply bitmap_bit_has_slot. }
    rewrite Hpresent.
    rewrite (@rank_lor_bitmap_bits_lt_left
      (chunk left_hash depth) (chunk right_hash depth)
      (chunk_bound left_hash depth) (chunk_bound right_hash depth) Hleft).
    cbn [dense_get]. now apply get_tree_leaf_same.
  - assert (Hright : N.ltb (chunk right_hash depth) (chunk left_hash depth) = true).
    { apply N.ltb_lt. apply N.ltb_ge in Hleft.
      destruct (N.eq_dec (chunk right_hash depth) (chunk left_hash depth))
        as [Hequal|Hunequal].
      - exfalso. apply Hdifferent. now symmetry.
      - lia. }
    cbn [get_tree].
    assert (Hpresent : bitmap_has
        (N.lor (bitmap_bit (chunk left_hash depth))
          (bitmap_bit (chunk right_hash depth)))
        (chunk left_hash depth) = true).
    { apply bitmap_has_lor_left. apply bitmap_bit_has_slot. }
    rewrite Hpresent.
    rewrite (N.lor_comm (bitmap_bit (chunk left_hash depth))
      (bitmap_bit (chunk right_hash depth))).
    rewrite (@rank_lor_bitmap_bits_lt_right
      (chunk right_hash depth) (chunk left_hash depth)
      (chunk_bound right_hash depth) (chunk_bound left_hash depth) Hright).
    cbn [dense_get]. now apply get_tree_leaf_same.
Qed.

Lemma get_tree_join_worker_left_leaf :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth left_hash right_hash
         (right : tree K A) (key : K) (value : A),
    eqb key key = true ->
    join_falls_back fuel depth left_hash right_hash = false ->
    get_tree eqb fuel depth left_hash key
      (join_worker fuel depth left_hash (Leaf left_hash key value) right_hash
        right) = Some value.
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth left_hash right_hash right key value
    Heqb Hfallback.
  - discriminate Hfallback.
  - cbn [join_worker join_falls_back] in Hfallback |-.
    destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth))
      eqn:Hchunks.
    + assert (Hsame : chunk left_hash depth = chunk right_hash depth).
      { now apply N.eqb_eq. }
      cbn [join_worker]. rewrite Hchunks.
      cbn [get_tree].
      rewrite child_bit_has_slot, child_bit_rank_self.
      cbn [dense_get].
      apply IH. exact Heqb. exact Hfallback.
    + cbn [join_worker]. rewrite Hchunks.
      apply get_tree_join_two_left_leaf; [exact Heqb|].
      now apply N.eqb_neq.
Qed.

Lemma get_tree_after_set_leaf_distinct_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) stored_hash stored (old_value : A),
    eqb key key = true ->
    eqb key stored = false ->
    full_hash <> stored_hash ->
    join_falls_back fuel depth full_hash stored_hash = false ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value
        (Leaf stored_hash stored old_value)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value stored_hash stored old_value
    Heqb Hmiss Hdifferent Hfallback.
  assert (Hhash : N.eqb full_hash stored_hash = false).
  { now apply N.eqb_neq. }
  destruct fuel as [|fuel]; cbn [set_tree].
  all: rewrite Hmiss, Hhash.
  all: apply get_tree_join_worker_left_leaf; assumption.
Qed.

Lemma get_tree_after_set_leaf_distinct_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) stored_hash stored (old_value : A),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    wf E hash seed depth prefix (Leaf stored_hash stored old_value) ->
    entry_matches hash seed full_hash depth prefix (key, value) ->
    eqb key stored = false ->
    full_hash <> stored_hash ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value
        (Leaf stored_hash stored old_value)) = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value
    stored_hash stored old_value Hfuel Hlength [Href Hsym Htrans] Heqb Hwf
    Hentry Hmiss Hdifferent.
  inversion Hwf as [|d p h s v Hstored_hash Hstored_bound Hstored_prefix| |];
    subst stored_hash.
  destruct Hentry as [Hkey_hash [Hkey_bound Hkey_prefix]].
  assert (Hself : eqb key key = true).
  { apply (proj2 (Heqb key key)). apply Href. }
  assert (Hprefix_agree : forall prior, prior < depth ->
      chunk full_hash prior = chunk (hash seed stored) prior).
  { intros prior Hprior.
    eapply prefix_matches_agree; eauto. }
  assert (Hfallback : join_falls_back fuel depth full_hash (hash seed stored) = false).
  { assert (Hfuel' : fuel = branch_levels - depth).
    { symmetry. apply Nat.add_sub_eq_l. exact Hfuel. }
    rewrite Hfuel'.
    apply join_worker_suffix_no_fallback; try assumption.
    - rewrite <- Hfuel. lia.
    }
  eapply get_tree_after_set_leaf_distinct_self; eauto.
Qed.

Lemma get_tree_after_set_collision_distinct_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) stored_hash (entries : list (K * A)),
    eqb key key = true ->
    full_hash <> stored_hash ->
    join_falls_back fuel depth full_hash stored_hash = false ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value
        (Collision stored_hash entries)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value stored_hash entries
    Heqb Hdifferent Hfallback.
  assert (Hhash : N.eqb full_hash stored_hash = false).
  { now apply N.eqb_neq. }
  destruct fuel as [|fuel]; cbn [set_tree].
  all: rewrite Hhash.
  all: apply get_tree_join_worker_left_leaf; assumption.
Qed.

Lemma get_tree_after_set_collision_distinct_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) stored_hash (entries : list (K * A)),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    wf E hash seed depth prefix (Collision stored_hash entries) ->
    entry_matches hash seed full_hash depth prefix (key, value) ->
    full_hash <> stored_hash ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value
        (Collision stored_hash entries)) = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value
    stored_hash entries Hfuel Hlength [Href Hsym Htrans] Heqb Hwf Hentry
    Hdifferent.
  destruct Hentry as [Hkey_hash [Hkey_bound Hkey_prefix]].
  assert (Hself : eqb key key = true).
  { apply (proj2 (Heqb key key)). apply Href. }
  assert (Hprefix_agree : forall prior, prior < depth ->
      chunk full_hash prior = chunk stored_hash prior).
  { intros prior Hprior.
    eapply prefix_matches_agree; eauto using wf_collision_prefix_matches. }
  assert (Hfallback : join_falls_back fuel depth full_hash stored_hash = false).
  { assert (Hfuel' : fuel = branch_levels - depth).
    { symmetry. apply Nat.add_sub_eq_l. exact Hfuel. }
    rewrite Hfuel'.
    apply join_worker_suffix_no_fallback.
    - rewrite <- Hfuel. lia.
    - exact Hprefix_agree.
    - exact Hkey_bound.
    - exact (@wf_collision_hash_bound K Seed A E hash seed depth prefix
        stored_hash entries Hwf).
    - exact Hdifferent.
    }
  eapply get_tree_after_set_collision_distinct_self; eauto.
Qed.

Lemma get_tree_after_set_self_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) (t : tree K A),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix t ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value t) = Some value.
Proof.
  intros K Seed A E hash seed eqb fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash key value t
    Hfuel Hlength Hequiv Heqb Hcongruent Hhash Hbound Hprefixmatch Hwf;
    pose proof Hequiv as [Href Hsym Htrans];
    destruct t as [|stored_hash stored old_value|stored_hash entries|bitmap children].
  - cbn [set_tree]. apply get_tree_leaf_same.
    apply (proj2 (Heqb key key)). apply Href.
  - destruct (N.eqb full_hash stored_hash) eqn:Hstored_hash.
    + apply N.eqb_eq in Hstored_hash. subst stored_hash.
      destruct (eqb key stored) eqn:Hkey.
      * rewrite (@set_tree_leaf_replaces_representative K A eqb 0 depth
          full_hash key stored old_value value Hkey).
        cbn [get_tree]. now rewrite N.eqb_refl, Hkey.
      * assert (Hself : eqb key key = true).
        { apply (proj2 (Heqb key key)). apply Href. }
        assert (Hset : set_tree eqb 0 depth full_hash key value
            (Leaf full_hash stored old_value) =
          Collision full_hash [(stored, old_value); (key, value)]).
        { cbn [set_tree]. now rewrite Hkey, N.eqb_refl. }
        rewrite Hset.
        rewrite get_tree_collision_same_hash.
        cbn [bucket_get]. now rewrite Hkey, Hself.
    + apply N.eqb_neq in Hstored_hash.
      assert (Hstored : stored_hash = hash seed stored).
      { inversion Hwf; assumption. }
      assert (Hmiss : eqb key stored = false).
      { destruct (eqb key stored) eqn:Hkey; auto.
        exfalso. apply Hstored_hash.
        rewrite Hstored, Hhash. apply Hcongruent.
        apply (proj1 (Heqb key stored)). exact Hkey. }
      assert (Hentry : entry_matches hash seed full_hash depth prefix (key, value)).
      { unfold entry_matches. repeat split; assumption. }
      eapply get_tree_after_set_leaf_distinct_wf; eauto.
  - destruct (N.eqb full_hash stored_hash) eqn:Hstored_hash.
    + apply N.eqb_eq in Hstored_hash. subst stored_hash.
      rewrite set_tree_collision_same_hash.
      rewrite get_tree_normalize_collision_same_hash.
      apply bucket_get_after_set.
      intro query. apply (proj2 (Heqb query query)). apply Href.
    + apply N.eqb_neq in Hstored_hash.
      assert (Hentry : entry_matches hash seed full_hash depth prefix (key, value)).
      { unfold entry_matches. repeat split; assumption. }
      eapply get_tree_after_set_collision_distinct_wf; eauto.
  - exfalso.
    eapply (@wf_branch_impossible_at_or_beyond_limit K Seed A E hash seed
      depth prefix bitmap children).
    + rewrite <- Hfuel. lia.
    + exact Hwf.
  - cbn [set_tree]. apply get_tree_leaf_same.
    apply (proj2 (Heqb key key)). apply Href.
  - destruct (N.eqb full_hash stored_hash) eqn:Hstored_hash.
    + apply N.eqb_eq in Hstored_hash. subst stored_hash.
      destruct (eqb key stored) eqn:Hkey.
      * rewrite (@set_tree_leaf_replaces_representative K A eqb (S fuel) depth
          full_hash key stored old_value value Hkey).
        cbn [get_tree]. now rewrite N.eqb_refl, Hkey.
      * assert (Hself : eqb key key = true).
        { apply (proj2 (Heqb key key)). apply Href. }
        assert (Hset : set_tree eqb (S fuel) depth full_hash key value
            (Leaf full_hash stored old_value) =
          Collision full_hash [(stored, old_value); (key, value)]).
        { cbn [set_tree]. now rewrite Hkey, N.eqb_refl. }
        rewrite Hset.
        rewrite get_tree_collision_same_hash.
        cbn [bucket_get]. now rewrite Hkey, Hself.
    + apply N.eqb_neq in Hstored_hash.
      assert (Hstored : stored_hash = hash seed stored).
      { inversion Hwf; assumption. }
      assert (Hmiss : eqb key stored = false).
      { destruct (eqb key stored) eqn:Hkey; auto.
        exfalso. apply Hstored_hash.
        rewrite Hstored, Hhash. apply Hcongruent.
        apply (proj1 (Heqb key stored)). exact Hkey. }
      assert (Hentry : entry_matches hash seed full_hash depth prefix (key, value)).
      { unfold entry_matches. repeat split; assumption. }
      eapply get_tree_after_set_leaf_distinct_wf; eauto.
  - destruct (N.eqb full_hash stored_hash) eqn:Hstored_hash.
    + apply N.eqb_eq in Hstored_hash. subst stored_hash.
      rewrite set_tree_collision_same_hash.
      rewrite get_tree_normalize_collision_same_hash.
      apply bucket_get_after_set.
      intro query. apply (proj2 (Heqb query query)). apply Href.
    + apply N.eqb_neq in Hstored_hash.
      assert (Hentry : entry_matches hash seed full_hash depth prefix (key, value)).
      { unfold entry_matches. repeat split; assumption. }
      eapply get_tree_after_set_collision_distinct_wf; eauto.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hroute.
    + destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hroute)
        as [child [Hchild [Hnonempty Hchildwf]]].
      eapply get_tree_after_set_branch_child_self; eauto.
      eapply IH with (prefix := prefix ++ [chunk full_hash depth]); eauto.
      * rewrite <- Hfuel. lia.
      * rewrite app_length, Hlength. cbn. lia.
      * apply prefix_matches_append_slot; assumption.
    + eapply get_tree_after_set_branch_slot_absent_self_wf.
      * exact Hwf.
      * apply (proj2 (Heqb key key)). apply Href.
      * exact Hroute.
Qed.

Lemma set_tree_wf_nonempty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) (t : tree K A),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix t ->
    set_tree eqb fuel depth full_hash key value t <> Empty.
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value t
    Hfuel Hlength Hequiv Heqb Hcongruent Hhash Hbound Hprefixmatch Hwf Hempty.
  pose proof (@get_tree_after_set_self_wf K Seed A E hash seed eqb fuel depth
    prefix full_hash key value t Hfuel Hlength Hequiv Heqb Hcongruent Hhash
    Hbound Hprefixmatch Hwf) as Hget.
  rewrite Hempty, get_tree_empty in Hget.
  discriminate.
Qed.

Lemma set_tree_leaf_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key stored : K) (old_value value : A) stored_hash,
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix (Leaf stored_hash stored old_value) ->
    wf E hash seed depth prefix
      (set_tree eqb fuel depth full_hash key value
        (Leaf stored_hash stored old_value)).
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key stored
    old_value value stored_hash Hfuel Hlength [Href Hsym Htrans] Heqb Hcongruent
    Hhash Hbound Hprefix Hwf.
  destruct (eqb key stored) eqn:Hkey.
  - assert (Hsame : full_hash = stored_hash).
    { assert (Hstored_hash : stored_hash = hash seed stored).
      { inversion Hwf; assumption. }
      rewrite Hstored_hash, Hhash.
      apply Hcongruent. apply (proj1 (Heqb key stored)). exact Hkey. }
    subst stored_hash.
    eapply set_tree_leaf_replacement_wf; eauto.
  - destruct (N.eqb full_hash stored_hash) eqn:Hsame.
    + apply N.eqb_eq in Hsame. subst stored_hash.
      eapply set_tree_leaf_collision_wf.
      * exact Hwf.
      * unfold entry_matches. repeat split; assumption.
      * exact Hkey.
      * intro Hrelated.
        assert (Htrue : eqb key stored = true).
        { apply (proj2 (Heqb key stored)). apply Hsym. exact Hrelated. }
        now rewrite Hkey in Htrue.
    + apply N.eqb_neq in Hsame.
      assert (Hsameb : N.eqb full_hash stored_hash = false).
      { apply N.eqb_neq. exact Hsame. }
      assert (Hnew : wf E hash seed depth prefix (Leaf full_hash key value)).
      { apply wf_leaf; assumption. }
      assert (Hstored_hash : stored_hash = hash seed stored).
      { inversion Hwf; assumption. }
      assert (Hstored_bound : (stored_hash < hash_space)%N).
      { inversion Hwf; assumption. }
      assert (Hstored_prefix : prefix_matches stored_hash depth prefix).
      { inversion Hwf; assumption. }
      assert (Hfallback : join_falls_back fuel depth full_hash stored_hash = false).
      { assert (Hfuel' : fuel = branch_levels - depth) by lia.
        rewrite Hfuel'. eapply join_worker_suffix_no_fallback.
        - lia.
        - intros prior Hprior.
          eapply prefix_matches_agree; eauto.
        - exact Hbound.
        - exact Hstored_bound.
        - exact Hsame. }
      destruct fuel as [|fuel].
      * cbn [set_tree]. rewrite Hkey, Hsameb.
        eapply wf_join_worker_leaf_leaf.
        -- lia.
        -- exact Hlength.
        -- exact Hsame.
        -- exact Hnew.
        -- exact Hwf.
        -- repeat split; assumption.
        -- exact Hcongruent.
        -- exact Hfallback.
      * cbn [set_tree]. rewrite Hkey, Hsameb.
        eapply wf_join_worker_leaf_leaf.
        -- lia.
        -- exact Hlength.
        -- exact Hsame.
        -- exact Hnew.
        -- exact Hwf.
        -- repeat split; assumption.
        -- exact Hcongruent.
        -- exact Hfallback.
Qed.

Lemma set_tree_collision_wf_general :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) stored_hash (entries : list (K * A)),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix (Collision stored_hash entries) ->
    wf E hash seed depth prefix
      (set_tree eqb fuel depth full_hash key value
        (Collision stored_hash entries)).
Proof.
  intros K Seed A E hash seed eqb fuel depth prefix full_hash key value
    stored_hash entries Hfuel Hlength [Href Hsym Htrans] Heqb Hcongruent Hhash
    Hbound Hprefix Hwf.
  destruct (N.eqb full_hash stored_hash) eqn:Hsame.
  - apply N.eqb_eq in Hsame. subst stored_hash.
    eapply set_tree_collision_wf.
    + exact Hwf.
    + intro Hnone. unfold entry_matches. repeat split; assumption.
    + exact Hsym.
    + intros Hnone Hin.
      apply (proj1 (InA_alt (binding_equiv E) (key, value) entries)) in Hin.
      destruct Hin as [[stored old_value] [Hrelated Hin]].
      assert (Hfalse : eqb key stored = false).
      { now apply (bucket_get_none_miss eqb key entries Hnone stored old_value). }
      assert (Htrue : eqb key stored = true).
      { apply (proj2 (Heqb key stored)). exact Hrelated. }
      now rewrite Hfalse in Htrue.
  - apply N.eqb_neq in Hsame.
    assert (Hsameb : N.eqb full_hash stored_hash = false).
    { apply N.eqb_neq. exact Hsame. }
    assert (Hnew : wf E hash seed depth prefix (Leaf full_hash key value)).
    { apply wf_leaf; assumption. }
    assert (Hstored_bound : (stored_hash < hash_space)%N).
    { eapply wf_collision_hash_bound; exact Hwf. }
    assert (Hstored_prefix : prefix_matches stored_hash depth prefix).
    { eapply wf_collision_prefix_matches; exact Hwf. }
    assert (Hfallback : join_falls_back fuel depth full_hash stored_hash = false).
    { assert (Hfuel' : fuel = branch_levels - depth) by lia.
      rewrite Hfuel'. eapply join_worker_suffix_no_fallback.
      - lia.
      - intros prior Hprior. eapply prefix_matches_agree; eauto.
      - exact Hbound.
      - exact Hstored_bound.
      - exact Hsame. }
    destruct fuel as [|fuel].
    + cbn [set_tree]. rewrite Hsameb.
      eapply wf_join_worker_leaf_collision.
      * lia.
      * exact Hlength.
      * exact Hsame.
      * exact Hnew.
      * exact Hwf.
      * repeat split; assumption.
      * exact Hcongruent.
      * exact Hfallback.
    + cbn [set_tree]. rewrite Hsameb.
      eapply wf_join_worker_leaf_collision.
      * lia.
      * exact Hlength.
      * exact Hsame.
      * exact Hnew.
      * exact Hwf.
      * repeat split; assumption.
      * exact Hcongruent.
      * exact Hfallback.
Qed.

Lemma set_tree_wf_general :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) (t : tree K A),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second -> hash seed first = hash seed second) ->
    full_hash = hash seed key ->
    (full_hash < hash_space)%N ->
    prefix_matches full_hash depth prefix ->
    wf E hash seed depth prefix t ->
    wf E hash seed depth prefix (set_tree eqb fuel depth full_hash key value t).
Proof.
  intros K Seed A E hash seed eqb fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash key value t
    Hfuel Hlength Hequiv Heqb Hcongruent Hhash Hbound Hprefix Hwf.
  - destruct t as [|stored_hash stored old_value|stored_hash entries|bitmap children].
    + eapply set_tree_empty_wf. unfold entry_matches. repeat split; assumption.
    + eapply set_tree_leaf_wf; eauto.
    + eapply set_tree_collision_wf_general; eauto.
    + cbn [set_tree]. exact Hwf.
  - destruct t as [|stored_hash stored old_value|stored_hash entries|bitmap children].
    + eapply set_tree_empty_wf. unfold entry_matches. repeat split; assumption.
    + eapply set_tree_leaf_wf; eauto.
    + eapply set_tree_collision_wf_general; eauto.
    + destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hroute.
      * destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hroute)
          as [child [Hchild [Hchildnonempty Hchildwf]]].
        assert (Hnextlength : length (prefix ++ [chunk full_hash depth]) = S depth).
        { rewrite app_length, Hlength. cbn. lia. }
        assert (Hnextprefix : prefix_matches full_hash (S depth)
          (prefix ++ [chunk full_hash depth])).
        { apply prefix_matches_append_slot; assumption. }
        assert (Hupdatedwf : wf E hash seed (S depth)
          (prefix ++ [chunk full_hash depth])
          (set_tree eqb fuel (S depth) full_hash key value child)).
        { eapply IH; eauto; lia. }
        eapply set_tree_branch_child_wf_fresh with (child := child)
          (updated_child := set_tree eqb fuel (S depth) full_hash key value child).
        -- exact Hequiv.
        -- exact Hcongruent.
        -- exact Hwf.
        -- exact Hlength.
        -- exact Hhash.
        -- exact Hroute.
        -- exact Hchild.
        -- reflexivity.
        -- eapply set_tree_wf_nonempty; eauto; lia.
        -- exact Hupdatedwf.
      * eapply set_tree_branch_slot_absent_wf_leaf_fresh; eauto.
Qed.

Lemma table_wf_set :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (table_seed m) key < hash_space)%N ->
    table_wf E hash m ->
    table_wf E hash (set eqb hash key value m).
Proof.
  intros K Seed A E hash eqb key value [seed root] Hequiv Heqb Hcongruent
    Hbound Hwf.
  unfold table_wf, set in Hwf |-.
  cbn in Hwf |-.
  eapply set_tree_wf_general; eauto.
  - reflexivity.
Qed.

Lemma add_first_table_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    table_seed m = seed ->
    table_wf E hash m ->
    table_wf E hash (add_first eqb hash entries m).
Proof.
  intros K Seed A E hash seed eqb entries.
  induction entries as [|[key value] tail IH]; intros m Hequiv Heqb Hcongruent
    Hbound Hseed Hwf.
  - change (table_wf E hash m). exact Hwf.
  - rewrite add_first_cons.
    destruct (get eqb hash key m) eqn:Hget.
    + eapply (IH m Hequiv Heqb Hcongruent).
      * intros key' value' Hin. apply (Hbound key' value'). right. exact Hin.
      * exact Hseed.
      * exact Hwf.
    + eapply (IH (set eqb hash key value m) Hequiv Heqb Hcongruent).
      * intros key' value' Hin. apply (Hbound key' value'). right. exact Hin.
      * rewrite set_seed. exact Hseed.
      * eapply table_wf_set; eauto.
        rewrite Hseed. apply (Hbound key value). left. reflexivity.
Qed.

Lemma table_wf_of_list :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    table_wf E hash (of_list eqb hash seed entries).
Proof.
  intros K Seed A E hash seed eqb entries Hequiv Heqb Hcongruent Hbound.
  unfold of_list.
  eapply add_first_table_wf; eauto using table_wf_empty.
Qed.

Lemma of_list_elements_keys_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    NoDupA E (map fst (elements (of_list eqb hash seed entries))).
Proof.
  intros K Seed A E hash seed eqb entries Hequiv Heqb Hcongruent Hbound.
  apply (@elements_keys_nodup K Seed A E hash
    (of_list eqb hash seed entries)).
  eapply table_wf_of_list; eauto.
Qed.

Lemma get_of_list_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) query (value : A)
         (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (hash seed query < hash_space)%N ->
    (get eqb hash query (of_list eqb hash seed entries) = Some value <->
      exists stored, In (stored, value) (elements (of_list eqb hash seed entries))
        /\ E query stored).
Proof.
  intros K Seed A E hash seed eqb query value entries Hequiv Heqb Hcongruent
    Hentries Hquery.
  apply (@get_binding_iff K Seed A E hash eqb query value
    (of_list eqb hash seed entries) Hequiv Heqb Hcongruent).
  - rewrite of_list_seed. exact Hquery.
  - eapply table_wf_of_list; eauto.
Qed.

Lemma mem_of_list_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) query
         (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (hash seed query < hash_space)%N ->
    (mem eqb hash query (of_list eqb hash seed entries) = true <->
      exists stored value,
        In (stored, value) (elements (of_list eqb hash seed entries)) /\
        E query stored).
Proof.
  intros K Seed A E hash seed eqb query entries Hequiv Heqb Hcongruent
    Hentries Hquery.
  apply (@mem_binding_iff K Seed A E hash eqb query
    (of_list eqb hash seed entries) Hequiv Heqb Hcongruent).
  - rewrite of_list_seed. exact Hquery.
  - eapply table_wf_of_list; eauto.
Qed.

Lemma get_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (hash seed key < hash_space)%N ->
    wf E hash seed 0 [] t ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed; table_root := t |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb key value t Hequiv Heqb Hcongruent Hbound Hwf.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value t) = Some value).
  eapply get_tree_after_set_self_wf; eauto.
  - reflexivity.
  - exact I.
Qed.

Lemma mem_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (table_seed m) key < hash_space)%N ->
    table_wf E hash m ->
    mem eqb hash key (set eqb hash key value m) = true.
Proof.
  intros K Seed A E hash eqb key value [seed t] Hequiv Heqb Hcongruent Hbound Hwf.
  unfold mem.
  rewrite (@get_after_set_self K Seed A E hash seed eqb key value t
    Hequiv Heqb Hcongruent Hbound Hwf).
  reflexivity.
Qed.

Lemma get_after_set_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (query key : K) (value : A)
         (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    E query key ->
    (hash seed key < hash_space)%N ->
    wf E hash seed 0 [] t ->
    get eqb hash query
      (set eqb hash key value
        {| table_seed := seed; table_root := t |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb query key value t Hequiv Heqb Hcongruent
    Hrelated Hbound Hwf.
  rewrite (@get_query_equiv K Seed A E eqb hash query key
    (set eqb hash key value {| table_seed := seed; table_root := t |})
    Hequiv Heqb Hcongruent Hrelated).
  exact (@get_after_set_self K Seed A E hash seed eqb key value t
    Hequiv Heqb Hcongruent Hbound Hwf).
Qed.

Lemma of_list_first_wins_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (first_key second_key : K)
         (first_value second_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    E second_key first_key ->
    (hash seed first_key < hash_space)%N ->
    of_list eqb hash seed
      [(first_key, first_value); (second_key, second_value)] =
    singleton eqb hash seed first_key first_value.
Proof.
  intros K Seed A E hash seed eqb first_key second_key first_value second_value
    Hequiv Heqb Hcongruent Hrelated Hbound.
  assert (Hget : get eqb hash second_key
    (set eqb hash first_key first_value (empty seed)) = Some first_value).
  { eapply (@get_after_set_equiv K Seed A E hash seed eqb second_key first_key
      first_value Empty); eauto.
    apply wf_empty. }
  unfold of_list. rewrite add_first_cons.
  rewrite get_empty.
  change (add_first eqb hash [(second_key, second_value)]
    (set eqb hash first_key first_value (empty seed)) =
    singleton eqb hash seed first_key first_value).
  rewrite add_first_cons, Hget. reflexivity.
Qed.

Lemma mem_after_set_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (query key : K) (value : A)
         (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    E query key ->
    (hash seed key < hash_space)%N ->
    wf E hash seed 0 [] t ->
    mem eqb hash query
      (set eqb hash key value
        {| table_seed := seed; table_root := t |}) = true.
Proof.
  intros K Seed A E hash seed eqb query key value t Hequiv Heqb Hcongruent
    Hrelated Hbound Hwf.
  unfold mem.
  rewrite (@get_after_set_equiv K Seed A E hash seed eqb query key value t
    Hequiv Heqb Hcongruent Hrelated Hbound Hwf).
  reflexivity.
Qed.

Lemma get_tree_after_set_leaf_same_hash_miss_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) stored (old_value : A),
    eqb key key = true ->
    eqb key stored = false ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value
        (Leaf full_hash stored old_value)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value stored old_value Heqb Hmiss.
  destruct fuel; cbn [set_tree].
  all: rewrite Hmiss, N.eqb_refl; cbn [get_tree bucket_get].
  all: rewrite Hmiss, Heqb.
  all: now rewrite N.eqb_refl.
Qed.

Lemma get_tree_after_set_leaf_hit_self :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (value : A) stored (old_value : A),
    eqb key stored = true ->
    get_tree eqb fuel depth full_hash key
      (set_tree eqb fuel depth full_hash key value
        (Leaf full_hash stored old_value)) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value stored old_value Hhit.
  destruct fuel; cbn [set_tree].
  all: rewrite Hhit.
  all: cbn [get_tree].
  all: now rewrite N.eqb_refl, Hhit.
Qed.

Lemma get_after_set_leaf_distinct_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         stored_hash stored (old_value : A),
    eqb key key = true ->
    (hash seed key < hash_space)%N ->
    eqb key stored = false ->
    hash seed key <> stored_hash ->
    wf E hash seed 0 [] (Leaf stored_hash stored old_value) ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed;
           table_root := Leaf stored_hash stored old_value |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb key value stored_hash stored old_value
    Heqb Hkey_bound Hmiss Hdifferent Hwf.
  inversion Hwf as [|d p h s v Hstored_hash Hstored_bound Hprefix| |];
    subst stored_hash.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Leaf (hash seed stored) stored old_value)) = Some value).
  apply get_tree_after_set_leaf_distinct_self; try assumption.
  apply join_worker_six_no_fallback; assumption.
Qed.

Lemma get_after_set_collision_distinct_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         stored_hash (entries : list (K * A)),
    eqb key key = true ->
    (hash seed key < hash_space)%N ->
    hash seed key <> stored_hash ->
    wf E hash seed 0 [] (Collision stored_hash entries) ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed;
           table_root := Collision stored_hash entries |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb key value stored_hash entries
    Heqb Hkey_bound Hdifferent Hwf.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Collision stored_hash entries)) = Some value).
  apply get_tree_after_set_collision_distinct_self; try assumption.
  apply join_worker_six_no_fallback; try assumption.
  exact (@wf_collision_hash_bound K Seed A E hash seed 0 [] stored_hash
    entries Hwf).
Qed.

Lemma get_after_set_collision_same_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         stored_hash (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    hash seed key = stored_hash ->
    wf E hash seed 0 [] (Collision stored_hash entries) ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed;
           table_root := Collision stored_hash entries |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb key value stored_hash entries
    [Href Hsym Htrans] Heqb Hhash Hwf.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Collision stored_hash entries)) = Some value).
  rewrite Hhash.
  apply get_tree_collision_after_set.
  intro query. apply (proj2 (Heqb query query)). apply Href.
Qed.

Lemma get_after_set_leaf_same_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         stored_hash stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    hash seed key = stored_hash ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed;
           table_root := Leaf stored_hash stored old_value |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb key value stored_hash stored old_value
    [Href Hsym Htrans] Heqb Hhash.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Leaf stored_hash stored old_value)) = Some value).
  rewrite Hhash.
  destruct (eqb key stored) eqn:Hkey.
  - apply get_tree_after_set_leaf_hit_self. exact Hkey.
  - apply get_tree_after_set_leaf_same_hash_miss_self; [|exact Hkey].
    apply (proj2 (Heqb key key)). apply Href.
Qed.

Lemma table_wf_set_leaf_same_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         stored_hash stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    hash seed key = stored_hash ->
    table_wf E hash
      {| table_seed := seed;
         table_root := Leaf stored_hash stored old_value |} ->
    table_wf E hash
      (set eqb hash key value
        {| table_seed := seed;
           table_root := Leaf stored_hash stored old_value |}).
Proof.
  intros K Seed A E hash seed eqb key value stored_hash stored old_value
    [Href Hsym Htrans] Heqb Hhash Hwf.
  unfold table_wf, set in Hwf |-.
  cbn in Hwf.
  change (wf E hash seed 0 []
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Leaf stored_hash stored old_value))).
  rewrite Hhash.
  destruct (eqb key stored) eqn:Hkey.
  - eapply set_tree_leaf_replacement_wf; eauto.
  - eapply set_tree_leaf_collision_wf; [exact Hwf| |exact Hkey|].
    + unfold entry_matches. split; [now symmetry|].
      split; [|exact I].
      inversion Hwf as [|d p h k v Hstored_hash Hbound Hprefix| |]; subst.
      exact Hbound.
    + intro Hrelated.
      assert (Htrue : eqb key stored = true).
      { apply (proj2 (Heqb key stored)). apply Hsym. exact Hrelated. }
      now rewrite Hkey in Htrue.
Qed.

Lemma table_wf_set_collision_same_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         stored_hash (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    hash seed key = stored_hash ->
    table_wf E hash
      {| table_seed := seed;
         table_root := Collision stored_hash entries |} ->
    table_wf E hash
      (set eqb hash key value
        {| table_seed := seed;
           table_root := Collision stored_hash entries |}).
Proof.
  intros K Seed A E hash seed eqb key value stored_hash entries
    [Href Hsym Htrans] Heqb Hhash Hwf.
  unfold table_wf, set in Hwf |-.
  cbn in Hwf.
  change (wf E hash seed 0 []
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Collision stored_hash entries))).
  rewrite Hhash.
  eapply set_tree_collision_wf.
  - exact Hwf.
  - intro Hmiss.
    unfold entry_matches.
    split.
    + symmetry. exact Hhash.
    + split.
      * exact (@wf_collision_hash_bound K Seed A E hash seed 0 [] stored_hash
          entries Hwf).
      * exact I.
  - exact Hsym.
  - intros Hnone Hin.
    apply (proj1 (InA_alt (binding_equiv E) (key, value) entries)) in Hin.
    destruct Hin as [[stored old_value] [Hrelated Hin]].
    assert (Hfalse : eqb key stored = false).
    { now apply (bucket_get_none_miss eqb key entries Hnone stored old_value). }
    assert (Htrue : eqb key stored = true).
    { apply (proj2 (Heqb key stored)). exact Hrelated. }
    now rewrite Hfalse in Htrue.
Qed.

Lemma get_after_set_empty_root :
  forall (K Seed A : Type) (hash : Seed -> K -> N) (seed : Seed)
         (eqb : K -> K -> bool) (key : K) (value : A),
    eqb key key = true ->
    get eqb hash key
      (set eqb hash key value (empty (A := A) seed)) = Some value.
Proof.
  intros K Seed A hash seed eqb key value Heqb.
  unfold get, set, empty.
  cbn [set_tree get_tree].
  exact (get_tree_leaf_same eqb branch_levels 0 (hash seed key) key value Heqb).
Qed.

Lemma table_wf_set_empty_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A),
    (hash seed key < hash_space)%N ->
    table_wf E hash
      (set eqb hash key value (empty (A := A) seed)).
Proof.
  intros K Seed A E hash seed eqb key value Hbound.
  unfold table_wf, set, empty.
  cbn.
  apply wf_leaf; [reflexivity|exact Hbound|exact I].
Qed.

Lemma get_after_set_branch_slot_absent_root :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         bitmap (children : list (tree K A)),
    table_wf E hash
      {| table_seed := seed; table_root := Branch bitmap children |} ->
    eqb key key = true ->
    bitmap_has bitmap (chunk (hash seed key) 0) = false ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed; table_root := Branch bitmap children |}) = Some value.
Proof.
  intros K Seed A E hash seed eqb key value bitmap children Hwf Heqb Habsent.
  unfold table_wf in Hwf.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Branch bitmap children)) = Some value).
  change (get_tree eqb (S 5) 0 (hash seed key) key
    (set_tree eqb (S 5) 0 (hash seed key) key value
      (Branch bitmap children)) = Some value).
  eapply get_tree_after_set_branch_slot_absent_self_wf; eauto.
Qed.

Lemma get_after_set_branch_child_root :
  forall (K Seed A : Type) (hash : Seed -> K -> N) (seed : Seed)
         (eqb : K -> K -> bool) (key : K) (value : A)
         bitmap (children : list (tree K A)) child,
    bitmap_has bitmap (chunk (hash seed key) 0) = true ->
    dense_get (rank bitmap (chunk (hash seed key) 0)) children = Some child ->
    get_tree eqb 5 1 (hash seed key) key
      (set_tree eqb 5 1 (hash seed key) key value child) = Some value ->
    get eqb hash key
      (set eqb hash key value
        {| table_seed := seed; table_root := Branch bitmap children |}) = Some value.
Proof.
  intros K Seed A hash seed eqb key value bitmap children child
    Hpresent Hchild Hrecursive.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (set_tree eqb branch_levels 0 (hash seed key) key value
      (Branch bitmap children)) = Some value).
  change (get_tree eqb (S 5) 0 (hash seed key) key
    (set_tree eqb (S 5) 0 (hash seed key) key value
      (Branch bitmap children)) = Some value).
  eapply get_tree_after_set_branch_child_self; eauto.
Qed.

Lemma get_tree_after_remove_self_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    full_hash = hash seed key ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
    wf E hash seed depth prefix t ->
    get_tree eqb fuel depth full_hash key
      (remove_tree eqb fuel depth full_hash key t) = None.
Proof.
  intros K Seed A E hash seed eqb fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash key t
    Hequiv Heqb Hkey_hash Hcongruent Hwf; destruct t as
    [|stored_hash stored value|stored_hash entries|bitmap children].
  - reflexivity.
  - inversion Hwf as [|d p h s v Hstored_hash Hbound Hprefix| |];
      subst stored_hash.
    destruct (eqb key stored) eqn:Hkey_stored.
    + assert (Hhash : full_hash = hash seed stored).
      { rewrite Hkey_hash. apply Hcongruent.
        exact (proj1 (Heqb key stored) Hkey_stored). }
      cbn [remove_tree get_tree]. rewrite Hhash, N.eqb_refl, Hkey_stored.
      reflexivity.
    + apply get_tree_after_remove_leaf_miss. exact Hkey_stored.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + apply N.eqb_eq in Hhash. subst stored_hash.
      apply (@get_tree_after_remove_collision_self K Seed A E hash seed eqb
        0 depth prefix full_hash key entries Hequiv Heqb Hwf).
    + assert (Hremove :
          remove_tree eqb 0 depth full_hash key
            (Collision stored_hash entries) = Collision stored_hash entries).
      { cbn [remove_tree]. now rewrite Hhash. }
      rewrite Hremove.
      apply get_tree_collision_other_hash.
      now apply N.eqb_neq.
  - reflexivity.
  - reflexivity.
  - inversion Hwf as [|d p h s v Hstored_hash Hbound Hprefix| |];
      subst stored_hash.
    destruct (eqb key stored) eqn:Hkey_stored.
    + assert (Hhash : full_hash = hash seed stored).
      { rewrite Hkey_hash. apply Hcongruent.
        exact (proj1 (Heqb key stored) Hkey_stored). }
      cbn [remove_tree get_tree]. rewrite Hhash, N.eqb_refl, Hkey_stored.
      reflexivity.
    + apply get_tree_after_remove_leaf_miss. exact Hkey_stored.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + apply N.eqb_eq in Hhash. subst stored_hash.
      apply (@get_tree_after_remove_collision_self K Seed A E hash seed eqb
        (S fuel) depth prefix full_hash key entries Hequiv Heqb Hwf).
    + assert (Hremove :
          remove_tree eqb (S fuel) depth full_hash key
            (Collision stored_hash entries) = Collision stored_hash entries).
      { cbn [remove_tree]. now rewrite Hhash. }
      rewrite Hremove.
      apply get_tree_collision_other_hash.
      now apply N.eqb_neq.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    + destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth)
        Hpresent) as [child [Hchild [Hnonempty Hchildwf]]].
      destruct (remove_tree eqb fuel (S depth) full_hash key child)
        as [|child_hash child_key child_value|child_hash child_entries|child_bitmap child_children]
        eqn:Hremove.
      * rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
          children Hpresent Hchild).
        rewrite Hremove.
        apply get_tree_branch_remove_slot_none.
      * rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
          children Hpresent Hchild).
        rewrite Hremove.
        rewrite (@get_tree_branch_replace_same K A eqb fuel depth full_hash key
          bitmap children child (Leaf child_hash child_key child_value)
          Hpresent Hchild).
        rewrite <- Hremove.
        exact (IH (S depth) (prefix ++ [chunk full_hash depth]) full_hash key child
          Hequiv Heqb Hkey_hash Hcongruent Hchildwf).
      * rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
          children Hpresent Hchild).
        rewrite Hremove.
        rewrite (@get_tree_branch_replace_same K A eqb fuel depth full_hash key
          bitmap children child (Collision child_hash child_entries)
          Hpresent Hchild).
        rewrite <- Hremove.
        exact (IH (S depth) (prefix ++ [chunk full_hash depth]) full_hash key child
          Hequiv Heqb Hkey_hash Hcongruent Hchildwf).
      * rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
          children Hpresent Hchild).
        rewrite Hremove.
        rewrite (@get_tree_branch_replace_same K A eqb fuel depth full_hash key
          bitmap children child (Branch child_bitmap child_children)
          Hpresent Hchild).
        rewrite <- Hremove.
        exact (IH (S depth) (prefix ++ [chunk full_hash depth]) full_hash key child
          Hequiv Heqb Hkey_hash Hcongruent Hchildwf).
    + rewrite (remove_tree_branch_slot_absent eqb fuel depth full_hash key
        bitmap children Hpresent).
      now apply get_tree_branch_slot_absent.
Qed.

Lemma get_after_remove_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    table_wf E hash m ->
    get eqb hash key (remove eqb hash key m) = None.
Proof.
  intros K Seed A E hash eqb key [seed root] Hequiv Heqb Hcongruent Hwf.
  change (get_tree eqb branch_levels 0 (hash seed key) key
    (remove_tree eqb branch_levels 0 (hash seed key) key root) = None).
  apply (@get_tree_after_remove_self_wf K Seed A E hash seed eqb
    branch_levels 0 [] (hash seed key) key root Hequiv Heqb).
  - reflexivity.
  - intros first second Hrelated. apply Hcongruent. exact Hrelated.
  - exact Hwf.
Qed.

Lemma get_after_remove_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    E query key ->
    table_wf E hash m ->
    get eqb hash query (remove eqb hash key m) = None.
Proof.
  intros K Seed A E hash eqb query key m Hequiv Heqb Hcongruent Hrelated Hwf.
  rewrite (@get_query_equiv K Seed A E eqb hash query key
    (remove eqb hash key m) Hequiv Heqb Hcongruent Hrelated).
  apply (@get_after_remove_self K Seed A E hash eqb key m
    Hequiv Heqb Hcongruent Hwf).
Qed.

Lemma mem_after_remove_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    table_wf E hash m ->
    mem eqb hash key (remove eqb hash key m) = false.
Proof.
  intros K Seed A E hash eqb key m Hequiv Heqb Hcongruent Hwf.
  unfold mem.
  rewrite (@get_after_remove_self K Seed A E hash eqb key m
    Hequiv Heqb Hcongruent Hwf).
  reflexivity.
Qed.

Lemma mem_after_remove_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    E query key ->
    table_wf E hash m ->
    mem eqb hash query (remove eqb hash key m) = false.
Proof.
  intros K Seed A E hash eqb query key m Hequiv Heqb Hcongruent Hrelated Hwf.
  unfold mem.
  rewrite (@get_after_remove_equiv K Seed A E hash eqb query key m
    Hequiv Heqb Hcongruent Hrelated Hwf).
  reflexivity.
Qed.

(** Updating a collision bucket leaves each entry outside the updated
    equivalence class untouched, including its payload. *)
Lemma bucket_set_other_binding :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         key (value : A) entries stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    (In (stored, old_value) (bucket_set eqb key value entries) <->
     In (stored, old_value) entries).
Proof.
  intros K A E eqb key value entries.
  induction entries as [|[head head_value] tail IH];
    intros stored old_value [Href Hsym Htrans] Heqb Hother; simpl.
  - split; [|contradiction].
    intros [Hentry|[]]. inversion Hentry; subst.
    exfalso. apply Hother. apply Href.
  - assert (Hkey_stored : eqb key stored = false).
    { destruct (eqb key stored) eqn:Hmatch; auto.
      exfalso. apply Hother. apply Hsym.
      now apply (proj1 (Heqb key stored)). }
    destruct (eqb key head) eqn:Hhead.
    + assert (Hstored_head : eqb stored head = false).
      { destruct (eqb stored head) eqn:Hmatch; auto.
        exfalso. apply Hother.
        apply Htrans with (y := head).
        - now apply (proj1 (Heqb stored head)).
        - apply Hsym. now apply (proj1 (Heqb key head)). }
      assert (Hpair_new : (stored, old_value) <> (head, value)).
      { intro Heq. inversion Heq; subst.
        rewrite (proj2 (Heqb head head) (Href head)) in Hstored_head.
        discriminate. }
      assert (Hpair_old : (stored, old_value) <> (head, head_value)).
      { intro Heq. inversion Heq; subst.
        rewrite (proj2 (Heqb head head) (Href head)) in Hstored_head.
        discriminate. }
      simpl. split; intro Hin; destruct Hin as [Hentry|Htail].
      * exfalso. now apply Hpair_new.
      * now right.
      * exfalso. now apply Hpair_old.
      * now right.
    + simpl. destruct (eqb stored head) eqn:Hstored_head.
      * specialize (IH stored old_value
          (Build_Equivalence E Href Hsym Htrans) Heqb Hother).
        split; intro Hin; destruct Hin as [Hentry|Htail].
        -- now left.
        -- right. now apply (proj1 IH).
        -- now left.
        -- right. now apply (proj2 IH).
      * specialize (IH stored old_value
          (Build_Equivalence E Href Hsym Htrans) Heqb Hother).
        split; intro Hin; destruct Hin as [Hentry|Htail].
        -- now left.
        -- right. now apply (proj1 IH).
        -- now left.
        -- right. now apply (proj2 IH).
Qed.

(** Exact flattened-binding preservation for an entry whose stored key is
    outside the class updated by [set_tree]. *)
Lemma bindings_set_tree_other :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash key (value : A) (t : tree K A) stored old_value,
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    (In (stored, old_value)
       (bindings (set_tree eqb fuel depth full_hash key value t)) <->
     In (stored, old_value) (bindings t)).
Proof.
  intros K A E eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key value t stored old_value
    Hequiv Heqb Hother; destruct t as
    [|stored_hash leaf_key leaf_value|stored_hash entries|bitmap children].
  - destruct Hequiv as [Href Hsym Htrans].
    assert (Hpair : (stored, old_value) <> (key, value)).
    { intro Heq. inversion Heq; subst. apply Hother. apply Href. }
    cbn [set_tree]. simpl. split.
    + intro Hentry.
      destruct Hentry as [Hentry|[]].
      apply Hpair. exact (eq_sym Hentry).
    + intro Hempty. contradiction.
  - cbn [set_tree].
    assert (Hmiss : eqb key stored = false).
    { destruct Hequiv as [Href Hsym Htrans].
      destruct (eqb key stored) eqn:Hmatch; auto.
      exfalso. apply Hother. apply Hsym.
      now apply (proj1 (Heqb key stored)). }
    destruct (eqb key leaf_key) eqn:Hleaf.
    + destruct Hequiv as [Href Hsym Htrans].
      assert (Hstored_leaf : ~ E stored leaf_key).
      { intro Hrelated. apply Hother.
        apply Htrans with (y := leaf_key); [exact Hrelated|].
        apply Hsym. now apply (proj1 (Heqb key leaf_key)). }
      assert (Hpair_new : (stored, old_value) <> (leaf_key, value)).
      { intro Heq. inversion Heq; subst. apply Hstored_leaf. apply Href. }
      assert (Hpair_old : (stored, old_value) <> (leaf_key, leaf_value)).
      { intro Heq. inversion Heq; subst. apply Hstored_leaf. apply Href. }
      simpl. split; intro Hin; destruct Hin as [Hentry|[]].
      * exfalso. now apply Hpair_new.
      * exfalso. now apply Hpair_old.
    + destruct (N.eqb full_hash stored_hash) eqn:Hhash.
      * assert (Hpair : (stored, old_value) <> (key, value)).
        { intro Heq. inversion Heq; subst. apply Hother.
          destruct Hequiv as [Href Hsym Htrans]. apply Href. }
        simpl. split.
        -- intros [Hentry|Hkey].
           ++ now left.
           ++ destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
        -- intros [Hleaf_eq|[]]. left. exact Hleaf_eq.
      * rewrite bindings_join_worker. simpl.
        assert (Hpair : (stored, old_value) <> (key, value)).
        { intro Heq. inversion Heq; subst. apply Hother.
          destruct Hequiv as [Href Hsym Htrans]. apply Href. }
        split.
        -- intros [Hkey|Hleaf_entry].
           ++ destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
           ++ exact Hleaf_entry.
        -- intro Hleaf_entry. now right.
  - cbn [set_tree].
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + rewrite bindings_normalize_collision.
      exact (@bucket_set_other_binding K A E eqb key value entries stored old_value
        Hequiv Heqb Hother).
    + rewrite bindings_join_worker. simpl.
      assert (Hpair : (stored, old_value) <> (key, value)).
      { intro Heq. inversion Heq; subst. apply Hother.
        destruct Hequiv as [Href Hsym Htrans]. apply Href. }
      split.
      * intros [Hkey|Hold].
        -- destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
        -- exact Hold.
      * intro Hold. now right.
  - cbn [set_tree]. tauto.
  - destruct Hequiv as [Href Hsym Htrans].
    assert (Hpair : (stored, old_value) <> (key, value)).
    { intro Heq. inversion Heq; subst. apply Hother. apply Href. }
    cbn [set_tree]. simpl. split.
    + intro Hentry.
      destruct Hentry as [Hentry|[]].
      apply Hpair. exact (eq_sym Hentry).
    + intro Hempty. contradiction.
  - cbn [set_tree].
    assert (Hmiss : eqb key stored = false).
    { destruct Hequiv as [Href Hsym Htrans].
      destruct (eqb key stored) eqn:Hmatch; auto.
      exfalso. apply Hother. apply Hsym.
      now apply (proj1 (Heqb key stored)). }
    destruct (eqb key leaf_key) eqn:Hleaf.
    + destruct Hequiv as [Href Hsym Htrans].
      assert (Hstored_leaf : ~ E stored leaf_key).
      { intro Hrelated. apply Hother.
        apply Htrans with (y := leaf_key); [exact Hrelated|].
        apply Hsym. now apply (proj1 (Heqb key leaf_key)). }
      assert (Hpair_new : (stored, old_value) <> (leaf_key, value)).
      { intro Heq. inversion Heq; subst. apply Hstored_leaf. apply Href. }
      assert (Hpair_old : (stored, old_value) <> (leaf_key, leaf_value)).
      { intro Heq. inversion Heq; subst. apply Hstored_leaf. apply Href. }
      simpl. split; intro Hin; destruct Hin as [Hentry|[]].
      * exfalso. now apply Hpair_new.
      * exfalso. now apply Hpair_old.
    + destruct (N.eqb full_hash stored_hash) eqn:Hhash.
      * assert (Hpair : (stored, old_value) <> (key, value)).
        { intro Heq. inversion Heq; subst. apply Hother.
          destruct Hequiv as [Href Hsym Htrans]. apply Href. }
        simpl. split.
        -- intros [Hentry|Hkey].
           ++ now left.
           ++ destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
        -- intros [Hleaf_eq|[]]. left. exact Hleaf_eq.
      * rewrite bindings_join_worker. simpl.
        assert (Hpair : (stored, old_value) <> (key, value)).
        { intro Heq. inversion Heq; subst. apply Hother.
          destruct Hequiv as [Href Hsym Htrans]. apply Href. }
        split.
        -- intros [Hkey|Hleaf_entry].
           ++ destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
           ++ exact Hleaf_entry.
        -- intro Hleaf_entry. now right.
  - cbn [set_tree].
    destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + rewrite bindings_normalize_collision.
      exact (@bucket_set_other_binding K A E eqb key value entries stored old_value
        Hequiv Heqb Hother).
    + rewrite bindings_join_worker. simpl.
      assert (Hpair : (stored, old_value) <> (key, value)).
      { intro Heq. inversion Heq; subst. apply Hother.
        destruct Hequiv as [Href Hsym Htrans]. apply Href. }
      split.
      * intros [Hkey|Hold].
        -- destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
        -- exact Hold.
      * intro Hold. now right.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    + destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
        as [child|] eqn:Hchild.
      * rewrite (set_tree_branch_child eqb fuel depth full_hash key value bitmap
          children Hpresent Hchild).
        destruct (@bindings_dense_replace_split K A
          (rank bitmap (chunk full_hash depth))
          (set_tree eqb fuel (S depth) full_hash key value child) child children Hchild)
          as [before [after [Hbefore Hafter]]].
        simpl. rewrite Hbefore, Hafter.
        rewrite !in_app_iff.
        rewrite (@IH (S depth) full_hash key value child stored old_value
          Hequiv Heqb Hother).
        tauto.
      * rewrite (set_tree_branch_dense_missing eqb fuel depth full_hash key value
          bitmap children Hpresent Hchild).
        rewrite bindings_branch_insert. simpl.
        assert (Hpair : (stored, old_value) <> (key, value)).
        { intro Heq. inversion Heq; subst. apply Hother.
          destruct Hequiv as [Href Hsym Htrans]. apply Href. }
        split.
        -- intros [Hkey|Hold].
           ++ destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
           ++ exact Hold.
        -- intro Hold. now right.
    + rewrite (set_tree_branch_slot_absent eqb fuel depth full_hash key value
        bitmap children Hpresent).
      rewrite bindings_branch_insert. simpl.
      assert (Hpair : (stored, old_value) <> (key, value)).
      { intro Heq. inversion Heq; subst. apply Hother.
        destruct Hequiv as [Href Hsym Htrans]. apply Href. }
      split.
      * intros [Hkey|Hold].
        -- destruct Hkey as [Hkey|[]]. exfalso. apply Hpair. now symmetry.
        -- exact Hold.
      * intro Hold. now right.
Qed.

Lemma get_after_set_other :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (value : A)
         (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    ~ E query key ->
    (hash (table_seed m) query < hash_space)%N ->
    (hash (table_seed m) key < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query (set eqb hash key value m) = get eqb hash query m.
Proof.
  intros K Seed A E hash eqb query key value [seed root] Hequiv Heqb
    Hcongruent Hdifferent Hquery_bound Hkey_bound Hwf.
  assert (Hsetwf : table_wf E hash
      (set eqb hash key value {| table_seed := seed; table_root := root |})).
  { eapply table_wf_set; eauto. }
  destruct (get eqb hash query {| table_seed := seed; table_root := root |})
    as [old_value|] eqn:Hget.
  - apply (proj1 (@get_binding_iff K Seed A E hash eqb query old_value
      {| table_seed := seed; table_root := root |}
      Hequiv Heqb Hcongruent Hquery_bound Hwf)) in Hget.
    destruct Hget as [stored [Hstored Hquery_stored]].
    assert (Hstored_other : ~ E stored key).
    { intro Hstored_key. apply Hdifferent.
      destruct Hequiv as [Href Hsym Htrans].
      eapply Htrans; eauto. }
    assert (Hstored_set : In (stored, old_value)
      (elements (set eqb hash key value
        {| table_seed := seed; table_root := root |}))).
    { change (In (stored, old_value)
        (bindings (set_tree eqb branch_levels 0 (hash seed key) key value root))).
      apply (proj2 (@bindings_set_tree_other K A E eqb branch_levels 0
        (hash seed key) key value root stored old_value Hequiv Heqb Hstored_other)).
      exact Hstored. }
    eapply get_binding_complete; eauto.
  - destruct (get eqb hash query
      (set eqb hash key value {| table_seed := seed; table_root := root |}))
      as [new_value|] eqn:Hset_get; [|reflexivity].
    exfalso.
    apply (proj1 (@get_binding_iff K Seed A E hash eqb query new_value
      (set eqb hash key value {| table_seed := seed; table_root := root |})
      Hequiv Heqb Hcongruent Hquery_bound Hsetwf)) in Hset_get.
    destruct Hset_get as [stored [Hstored_set Hquery_stored]].
    assert (Hstored_other : ~ E stored key).
    { intro Hstored_key. apply Hdifferent.
      destruct Hequiv as [Href Hsym Htrans].
      eapply Htrans; eauto. }
    assert (Hstored : In (stored, new_value) (elements
      {| table_seed := seed; table_root := root |})).
    { change (In (stored, new_value)
        (bindings (set_tree eqb branch_levels 0 (hash seed key) key value root)))
      in Hstored_set.
      change (In (stored, new_value) (bindings root)).
      apply (proj1 (@bindings_set_tree_other K A E eqb branch_levels 0
        (hash seed key) key value root stored new_value Hequiv Heqb Hstored_other)).
      exact Hstored_set. }
    pose proof (@get_binding_complete K Seed A E hash eqb query stored new_value
      {| table_seed := seed; table_root := root |} Hequiv Heqb Hcongruent
      Hquery_bound Hwf Hstored Hquery_stored) as Hold_get.
    rewrite Hget in Hold_get. discriminate.
Qed.

Lemma get_after_set :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (value : A)
         (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (table_seed m) query < hash_space)%N ->
    (hash (table_seed m) key < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query (set eqb hash key value m) =
      if eqb query key then Some value else get eqb hash query m.
Proof.
  intros K Seed A E hash eqb query key value m Hequiv Heqb Hcongruent
    Hquery_bound Hkey_bound Hwf.
  destruct (eqb query key) eqn:Hquery_key.
  - apply get_after_set_equiv with (E := E); try assumption.
    now apply (proj1 (Heqb query key)).
  - apply get_after_set_other with (E := E); try assumption.
    intro Hrelated. apply (proj2 (Heqb query key)) in Hrelated.
    now rewrite Hquery_key in Hrelated.
Qed.

Lemma bucket_remove_other_binding :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         key entries stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    (In (stored, old_value) (bucket_remove eqb key entries) <->
     In (stored, old_value) entries).
Proof.
  intros K A E eqb key entries.
  induction entries as [|[head head_value] tail IH];
    intros stored old_value [Href Hsym Htrans] Heqb Hother; simpl.
  - tauto.
  - destruct (eqb key head) eqn:Hkey_head.
    + assert (Hstored_head : eqb stored head = false).
      { destruct (eqb stored head) eqn:Hmatch; auto.
        exfalso. apply Hother.
        apply Htrans with (y := head).
        - now apply (proj1 (Heqb stored head)).
        - apply Hsym. now apply (proj1 (Heqb key head)). }
      assert (Hpair : (stored, old_value) <> (head, head_value)).
      { intro Heq. inversion Heq; subst.
        rewrite (proj2 (Heqb head head) (Href head)) in Hstored_head.
        discriminate. }
      split.
      * intro Hin. simpl in Hin. simpl. right. exact Hin.
      * intros [Hentry|Hin].
        -- exfalso. apply Hpair. now symmetry.
        -- exact Hin.
    + specialize (IH stored old_value
        (Build_Equivalence E Href Hsym Htrans) Heqb Hother).
      split; intro Hin; simpl in Hin |-; destruct Hin as [Hentry|Htail].
      * now left.
      * right. now apply (proj1 IH).
      * now left.
      * right. now apply (proj2 IH).
Qed.

Lemma dense_remove_at_split :
  forall (X : Type) before (item : X) after,
    dense_remove (length before) (before ++ item :: after) = before ++ after.
Proof.
  intros X before. induction before as [|head before IH]; intros item after.
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

Lemma dense_get_remove_split :
  forall (X : Type) index (children : list X) child,
    dense_get index children = Some child ->
    exists before after,
      children = before ++ child :: after /\
      length before = index /\
      dense_remove index children = before ++ after.
Proof.
  intros X index. induction index as [|index IH]; intros children child Hget;
    destruct children as [|head tail].
  - discriminate.
  - simpl in Hget. inversion Hget; subst child.
    exists [], tail. repeat split; reflexivity.
  - discriminate.
  - simpl in Hget.
    destruct (IH tail child Hget) as [before [after [Hchildren [Hlength Hremove]]]].
    exists (head :: before), after. split.
    + simpl. now rewrite Hchildren.
    + split.
      * simpl. now rewrite Hlength.
      * simpl. now rewrite Hremove.
Qed.

Lemma bindings_remove_leaf_other_in :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash key stored_hash leaf_key (leaf_value : A)
         stored old_value,
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    In (stored, old_value) (bindings (Leaf stored_hash leaf_key leaf_value)) ->
    In (stored, old_value)
      (bindings (remove_tree eqb fuel depth full_hash key
        (Leaf stored_hash leaf_key leaf_value))).
Proof.
  intros K A E eqb fuel depth full_hash key stored_hash leaf_key leaf_value
    stored old_value [Href Hsym Htrans] Heqb Hother Hin.
  destruct (N.eqb full_hash stored_hash) eqn:Hhash.
  - destruct (eqb key leaf_key) eqn:Hkey.
    + assert (Hkey_related : E key leaf_key).
      { now apply (proj1 (Heqb key leaf_key)). }
      exfalso. simpl in Hin. destruct Hin as [Hentry|[]].
      inversion Hentry; subst. apply Hother. apply Hsym.
      exact Hkey_related.
    + destruct fuel; cbn [remove_tree]; now rewrite Hhash, Hkey.
  - destruct fuel; cbn [remove_tree]; now rewrite Hhash.
Qed.

Lemma bindings_remove_collision_other_in :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash key stored_hash entries stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    In (stored, old_value) (bindings (Collision stored_hash entries)) ->
    In (stored, old_value)
      (bindings (remove_tree eqb fuel depth full_hash key
        (Collision stored_hash entries))).
Proof.
  intros K A E eqb fuel depth full_hash key stored_hash entries stored old_value
    Hequiv Heqb Hother Hin.
  destruct (N.eqb full_hash stored_hash) eqn:Hhash.
  - apply N.eqb_eq in Hhash. subst stored_hash.
    rewrite remove_tree_collision_same_hash, bindings_normalize_collision.
    apply (proj2 (@bucket_remove_other_binding K A E eqb key entries stored old_value
      Hequiv Heqb Hother)).
    exact Hin.
  - destruct fuel; cbn [remove_tree]; now rewrite Hhash.
Qed.

Lemma bindings_remove_tree_other_in :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash key (t : tree K A) stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    In (stored, old_value) (bindings t) ->
    In (stored, old_value)
      (bindings (remove_tree eqb fuel depth full_hash key t)).
Proof.
  intros K A E eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key t stored old_value
    Hequiv Heqb Hother Hin; destruct t as
    [|stored_hash leaf_key leaf_value|stored_hash entries|bitmap children].
  - contradiction.
  - eapply bindings_remove_leaf_other_in; eauto.
  - eapply bindings_remove_collision_other_in; eauto.
  - cbn [remove_tree]. exact Hin.
  - contradiction.
  - eapply bindings_remove_leaf_other_in; eauto.
  - eapply bindings_remove_collision_other_in; eauto.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    + destruct (dense_get (rank bitmap (chunk full_hash depth)) children)
        as [child|] eqn:Hchild.
      * destruct (@dense_get_remove_split (tree K A)
          (rank bitmap (chunk full_hash depth)) children child Hchild)
          as [before [after [Hchildren [Hlength Hremove_dense]]]].
        change (In (stored, old_value) (flat_map bindings children)) in Hin.
        rewrite Hchildren in Hin.
        repeat rewrite flat_map_app in Hin.
        simpl in Hin.
        rewrite (remove_tree_branch_child eqb fuel depth full_hash key bitmap
          children Hpresent Hchild).
        remember (remove_tree eqb fuel (S depth) full_hash key child) as child'.
        assert (Hchild_preserved :
          In (stored, old_value) (bindings child) ->
          In (stored, old_value) (bindings child')).
        { intro Hchild_binding. subst child'.
          eapply IH; eauto. }
        destruct child' as
          [|child_hash child_key child_value|child_hash child_entries
           |child_bitmap child_children] eqn:Hchild'.
        -- unfold branch_remove. rewrite Hchildren, <- Hlength.
           rewrite dense_remove_at_split.
           repeat rewrite flat_map_app.
           apply in_app_iff in Hin.
           destruct Hin as [Hbefore|Hchild_after].
           ++ assert (Hremaining : In (stored, old_value)
                (flat_map bindings before ++ flat_map bindings after)).
              { apply (proj2 (in_app_iff _ _ _)). now left. }
              destruct (before ++ after) as [|head tail] eqn:Hremaining_nodes;
                [apply app_eq_nil in Hremaining_nodes;
                 destruct Hremaining_nodes as [Hbefore_empty Hafter_empty];
                 subst before; subst after; simpl in Hremaining; contradiction|].
              change (In (stored, old_value) (flat_map bindings (head :: tail))).
              rewrite <- Hremaining_nodes, flat_map_app. exact Hremaining.
           ++ apply in_app_iff in Hchild_after.
              destruct Hchild_after as [Hchild_binding|Hafter].
              ** specialize (Hchild_preserved Hchild_binding).
                 simpl in Hchild_preserved. contradiction.
              ** assert (Hremaining : In (stored, old_value)
                   (flat_map bindings before ++ flat_map bindings after)).
                 { apply (proj2 (in_app_iff _ _ _)). now right. }
                 destruct (before ++ after) as [|head tail] eqn:Hremaining_nodes;
                   [apply app_eq_nil in Hremaining_nodes;
                    destruct Hremaining_nodes as [Hbefore_empty Hafter_empty];
                    subst before; subst after; simpl in Hremaining; contradiction|].
                 change (In (stored, old_value) (flat_map bindings (head :: tail))).
                 rewrite <- Hremaining_nodes, flat_map_app. exact Hremaining.
        -- unfold branch_replace. simpl.
           rewrite Hchildren, <- Hlength.
           rewrite dense_replace_at_split by reflexivity.
           repeat rewrite flat_map_app.
           change (In (stored, old_value)
             (flat_map bindings before ++
              (bindings (Leaf child_hash child_key child_value) ++ flat_map bindings after))).
           change (In (stored, old_value)
             (flat_map bindings before ++ (bindings child ++ flat_map bindings after))) in Hin.
           assert (Hsplit : In (stored, old_value) (flat_map bindings before) \/
             In (stored, old_value) (bindings child ++ flat_map bindings after)).
           { exact (proj1 (in_app_iff _ _ _) Hin). }
           destruct Hsplit as [Hbefore|Hchild_after].
           ++ apply (proj2 (in_app_iff (flat_map bindings before)
                (bindings (Leaf child_hash child_key child_value) ++ flat_map bindings after)
                (stored, old_value))). now left.
           ++ assert (Hsplit_child : In (stored, old_value) (bindings child) \/
                In (stored, old_value) (flat_map bindings after)).
              { exact (proj1 (in_app_iff _ _ _) Hchild_after). }
              destruct Hsplit_child as [Hchild_binding|Hafter].
              ** apply (proj2 (in_app_iff (flat_map bindings before)
                   (bindings (Leaf child_hash child_key child_value) ++ flat_map bindings after)
                   (stored, old_value))). right.
                 apply (proj2 (in_app_iff (bindings (Leaf child_hash child_key child_value))
                   (flat_map bindings after) (stored, old_value))). left.
                 now apply Hchild_preserved.
              ** apply (proj2 (in_app_iff (flat_map bindings before)
                   (bindings (Leaf child_hash child_key child_value) ++ flat_map bindings after)
                   (stored, old_value))). right.
                 apply (proj2 (in_app_iff (bindings (Leaf child_hash child_key child_value))
                   (flat_map bindings after) (stored, old_value))). now right.
        -- unfold branch_replace. simpl.
           rewrite Hchildren, <- Hlength.
           rewrite dense_replace_at_split by reflexivity.
           repeat rewrite flat_map_app.
           change (In (stored, old_value)
             (flat_map bindings before ++
              (bindings (Collision child_hash child_entries) ++ flat_map bindings after))).
           change (In (stored, old_value)
             (flat_map bindings before ++ (bindings child ++ flat_map bindings after))) in Hin.
           assert (Hsplit : In (stored, old_value) (flat_map bindings before) \/
             In (stored, old_value) (bindings child ++ flat_map bindings after)).
           { exact (proj1 (in_app_iff _ _ _) Hin). }
           destruct Hsplit as [Hbefore|Hchild_after].
           ++ apply (proj2 (in_app_iff (flat_map bindings before)
                (bindings (Collision child_hash child_entries) ++ flat_map bindings after)
                (stored, old_value))). now left.
           ++ assert (Hsplit_child : In (stored, old_value) (bindings child) \/
                In (stored, old_value) (flat_map bindings after)).
              { exact (proj1 (in_app_iff _ _ _) Hchild_after). }
              destruct Hsplit_child as [Hchild_binding|Hafter].
              ** apply (proj2 (in_app_iff (flat_map bindings before)
                   (bindings (Collision child_hash child_entries) ++ flat_map bindings after)
                   (stored, old_value))). right.
                 apply (proj2 (in_app_iff (bindings (Collision child_hash child_entries))
                   (flat_map bindings after) (stored, old_value))). left.
                 now apply Hchild_preserved.
              ** apply (proj2 (in_app_iff (flat_map bindings before)
                   (bindings (Collision child_hash child_entries) ++ flat_map bindings after)
                   (stored, old_value))). right.
                 apply (proj2 (in_app_iff (bindings (Collision child_hash child_entries))
                   (flat_map bindings after) (stored, old_value))). now right.
        -- unfold branch_replace. simpl.
           rewrite Hchildren, <- Hlength.
           rewrite dense_replace_at_split by reflexivity.
           repeat rewrite flat_map_app.
           change (In (stored, old_value)
             (flat_map bindings before ++
              (bindings (Branch child_bitmap child_children) ++ flat_map bindings after))).
           change (In (stored, old_value)
             (flat_map bindings before ++ (bindings child ++ flat_map bindings after))) in Hin.
           assert (Hsplit : In (stored, old_value) (flat_map bindings before) \/
             In (stored, old_value) (bindings child ++ flat_map bindings after)).
           { exact (proj1 (in_app_iff _ _ _) Hin). }
           destruct Hsplit as [Hbefore|Hchild_after].
           ++ apply (proj2 (in_app_iff (flat_map bindings before)
                (bindings (Branch child_bitmap child_children) ++ flat_map bindings after)
                (stored, old_value))). now left.
           ++ assert (Hsplit_child : In (stored, old_value) (bindings child) \/
                In (stored, old_value) (flat_map bindings after)).
              { exact (proj1 (in_app_iff _ _ _) Hchild_after). }
              destruct Hsplit_child as [Hchild_binding|Hafter].
              ** apply (proj2 (in_app_iff (flat_map bindings before)
                   (bindings (Branch child_bitmap child_children) ++ flat_map bindings after)
                   (stored, old_value))). right.
                 apply (proj2 (in_app_iff (bindings (Branch child_bitmap child_children))
                   (flat_map bindings after) (stored, old_value))). left.
                 now apply Hchild_preserved.
              ** apply (proj2 (in_app_iff (flat_map bindings before)
                   (bindings (Branch child_bitmap child_children) ++ flat_map bindings after)
                   (stored, old_value))). right.
                 apply (proj2 (in_app_iff (bindings (Branch child_bitmap child_children))
                   (flat_map bindings after) (stored, old_value))). now right.
      * rewrite (remove_tree_branch_dense_missing eqb fuel depth full_hash key
          bitmap children Hpresent Hchild).
        exact Hin.
    + rewrite (remove_tree_branch_slot_absent eqb fuel depth full_hash key
        bitmap children Hpresent).
      exact Hin.
Qed.

Lemma bindings_remove_tree_other :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash key (t : tree K A) stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    (In (stored, old_value)
       (bindings (remove_tree eqb fuel depth full_hash key t)) <->
     In (stored, old_value) (bindings t)).
Proof.
  intros K A E eqb fuel depth full_hash key t stored old_value
    Hequiv Heqb Hother.
  split.
  - apply bindings_remove_tree_in.
  - eapply bindings_remove_tree_other_in; eauto.
Qed.

Lemma get_after_remove_other :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    ~ E query key ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query (remove eqb hash key m) = get eqb hash query m.
Proof.
  intros K Seed A E hash eqb query key [seed root] Hequiv Heqb Hcongruent
    Hdifferent Hquery_bound Hwf.
  assert (Hremwf : table_wf E hash
      (remove eqb hash key {| table_seed := seed; table_root := root |})).
  { eapply table_wf_remove; eauto. }
  destruct (get eqb hash query {| table_seed := seed; table_root := root |})
    as [old_value|] eqn:Hget.
  - apply (proj1 (@get_binding_iff K Seed A E hash eqb query old_value
      {| table_seed := seed; table_root := root |}
      Hequiv Heqb Hcongruent Hquery_bound Hwf)) in Hget.
    destruct Hget as [stored [Hstored Hquery_stored]].
    assert (Hstored_other : ~ E stored key).
    { intro Hstored_key. apply Hdifferent.
      destruct Hequiv as [Href Hsym Htrans].
      eapply Htrans; eauto. }
    assert (Hstored_removed : In (stored, old_value)
      (elements (remove eqb hash key
        {| table_seed := seed; table_root := root |}))).
    { change (In (stored, old_value)
        (bindings (remove_tree eqb branch_levels 0 (hash seed key) key root))).
      apply (proj2 (@bindings_remove_tree_other K A E eqb branch_levels 0
        (hash seed key) key root stored old_value Hequiv Heqb Hstored_other)).
      exact Hstored. }
    eapply get_binding_complete; eauto.
  - destruct (get eqb hash query
      (remove eqb hash key {| table_seed := seed; table_root := root |}))
      as [new_value|] eqn:Hrem_get; [|reflexivity].
    exfalso.
    apply (proj1 (@get_binding_iff K Seed A E hash eqb query new_value
      (remove eqb hash key {| table_seed := seed; table_root := root |})
      Hequiv Heqb Hcongruent Hquery_bound Hremwf)) in Hrem_get.
    destruct Hrem_get as [stored [Hstored_removed Hquery_stored]].
    assert (Hstored_other : ~ E stored key).
    { intro Hstored_key. apply Hdifferent.
      destruct Hequiv as [Href Hsym Htrans].
      eapply Htrans; eauto. }
    assert (Hstored : In (stored, new_value) (elements
      {| table_seed := seed; table_root := root |})).
    { change (In (stored, new_value)
        (bindings (remove_tree eqb branch_levels 0 (hash seed key) key root)))
      in Hstored_removed.
      change (In (stored, new_value) (bindings root)).
      apply (proj1 (@bindings_remove_tree_other K A E eqb branch_levels 0
        (hash seed key) key root stored new_value Hequiv Heqb Hstored_other)).
      exact Hstored_removed. }
    pose proof (@get_binding_complete K Seed A E hash eqb query stored new_value
      {| table_seed := seed; table_root := root |} Hequiv Heqb Hcongruent
      Hquery_bound Hwf Hstored Hquery_stored) as Hold_get.
    rewrite Hget in Hold_get. discriminate.
Qed.

Lemma get_after_remove :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query (remove eqb hash key m) =
      if eqb query key then None else get eqb hash query m.
Proof.
  intros K Seed A E hash eqb query key m Hequiv Heqb Hcongruent
    Hquery_bound Hwf.
  destruct (eqb query key) eqn:Hquery_key.
  - apply get_after_remove_equiv with (E := E); try assumption.
    now apply (proj1 (Heqb query key)).
  - apply get_after_remove_other with (E := E); try assumption.
    intro Hrelated. apply (proj2 (Heqb query key)) in Hrelated.
    now rewrite Hquery_key in Hrelated.
Qed.

Lemma get_add_first_present :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (entries : list (K * A))
         (m : table K Seed A) (query : K) (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (forall key value, In (key, value) entries ->
      (hash (table_seed m) key < hash_space)%N) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query m = Some old_value ->
    get eqb hash query (add_first eqb hash entries m) = Some old_value.
Proof.
  intros K Seed A E hash eqb entries.
  induction entries as [|[key value] tail IH];
    intros m query old_value Hequiv Heqb Hcongruent Hbound Hquery_bound Hwf Hget.
  - exact Hget.
  - rewrite add_first_cons.
    destruct (get eqb hash key m) eqn:Hkey.
    + eapply IH; eauto.
      intros key' value' Hin. apply (Hbound key' value'). now right.
    + assert (Hquery_key : eqb query key = false).
      { destruct (eqb query key) eqn:Hquery_key; auto.
        exfalso.
        pose proof (@get_query_equiv K Seed A E eqb hash query key m
          Hequiv Heqb Hcongruent
          (proj1 (Heqb query key) Hquery_key)) as Hsame.
        rewrite Hget in Hsame. rewrite Hkey in Hsame. discriminate. }
      apply (IH (set eqb hash key value m) query old_value Hequiv Heqb Hcongruent).
      * intros key' value' Hin.
        rewrite set_seed. apply (Hbound key' value'). now right.
      * rewrite set_seed. exact Hquery_bound.
      * eapply table_wf_set; eauto.
        apply (Hbound key value). now left.
      * rewrite (@get_after_set K Seed A E hash eqb query key value m
          Hequiv Heqb Hcongruent Hquery_bound
          (Hbound key value (or_introl eq_refl)) Hwf).
        now rewrite Hquery_key.
Qed.

Lemma get_add_first :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (entries : list (K * A))
         (m : table K Seed A) (query : K),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (forall key value, In (key, value) entries ->
      (hash (table_seed m) key < hash_space)%N) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query (add_first eqb hash entries m) =
      match get eqb hash query m with
      | Some value => Some value
      | None => option_map snd (first_binding eqb query entries)
      end.
Proof.
  intros K Seed A E hash eqb entries.
  induction entries as [|[key value] tail IH];
    intros m query Hequiv Heqb Hcongruent Hbound Hquery_bound Hwf.
  - simpl [add_first]. destruct (get eqb hash query m); reflexivity.
  - destruct (get eqb hash query m) as [old_value|] eqn:Hquery.
    + change (get eqb hash query (add_first eqb hash ((key, value) :: tail) m) =
        Some old_value).
      eapply get_add_first_present; eauto.
    + rewrite add_first_cons. simpl first_binding.
      destruct (eqb query key) eqn:Hquery_key.
      * assert (Hkey : get eqb hash key m = None).
        { pose proof (@get_query_equiv K Seed A E eqb hash query key m
            Hequiv Heqb Hcongruent
            (proj1 (Heqb query key) Hquery_key)) as Hsame.
          rewrite Hquery in Hsame. now symmetry. }
        rewrite Hkey.
        eapply get_add_first_present.
        -- exact Hequiv.
        -- exact Heqb.
        -- exact Hcongruent.
        -- intros key' value' Hin.
           rewrite set_seed. apply (Hbound key' value'). now right.
        -- rewrite set_seed. exact Hquery_bound.
        -- eapply table_wf_set; eauto.
           apply (Hbound key value). now left.
        -- rewrite (@get_after_set K Seed A E hash eqb query key value m
             Hequiv Heqb Hcongruent Hquery_bound
             (Hbound key value (or_introl eq_refl)) Hwf).
           now rewrite Hquery_key.
      * destruct (get eqb hash key m) as [previous|] eqn:Hkey.
        -- pose proof (IH m query Hequiv Heqb Hcongruent
             (fun key' value' Hin => Hbound key' value' (or_intror Hin))
             Hquery_bound Hwf) as Htail.
           rewrite Hquery in Htail. exact Htail.
        -- assert (Hquery_set : get eqb hash query
             (set eqb hash key value m) = None).
           { rewrite (@get_after_set K Seed A E hash eqb query key value m
                Hequiv Heqb Hcongruent Hquery_bound
                (Hbound key value (or_introl eq_refl)) Hwf).
             now rewrite Hquery_key. }
           assert (Hbound_tail_set : forall key' value', In (key', value') tail ->
             (hash (table_seed (set eqb hash key value m)) key' < hash_space)%N).
           { intros key' value' Hin. rewrite set_seed.
             apply (Hbound key' value'). now right. }
           assert (Hquery_bound_set :
             (hash (table_seed (set eqb hash key value m)) query < hash_space)%N).
           { rewrite set_seed. exact Hquery_bound. }
           assert (Hwf_set : table_wf E hash (set eqb hash key value m)).
           { eapply table_wf_set; eauto.
             apply (Hbound key value). now left. }
           pose proof (IH (set eqb hash key value m) query Hequiv Heqb Hcongruent
             Hbound_tail_set Hquery_bound_set Hwf_set) as Htail.
           rewrite Hquery_set in Htail. exact Htail.
Qed.

Lemma get_of_list_first_binding :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         (query : K),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (hash seed query < hash_space)%N ->
    get eqb hash query (of_list eqb hash seed entries) =
      option_map snd (first_binding eqb query entries).
Proof.
  intros K Seed A E hash seed eqb entries query Hequiv Heqb Hcongruent
    Hbound Hquery_bound.
  unfold of_list.
  pose proof (@get_add_first K Seed A E hash eqb entries (empty seed) query
    Hequiv Heqb Hcongruent Hbound Hquery_bound
    (table_wf_empty E hash seed)) as Hget.
  rewrite get_empty in Hget. exact Hget.
Qed.

Lemma mem_of_list_first_binding :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         (query : K),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (hash seed query < hash_space)%N ->
    mem eqb hash query (of_list eqb hash seed entries) =
      match first_binding eqb query entries with
      | Some _ => true
      | None => false
      end.
Proof.
  intros K Seed A E hash seed eqb entries query Hequiv Heqb Hcongruent
    Hbound Hquery_bound.
  unfold mem.
  rewrite (@get_of_list_first_binding K Seed A E hash seed eqb entries query
    Hequiv Heqb Hcongruent Hbound Hquery_bound).
  destruct (first_binding eqb query entries) as [[stored value]|]; reflexivity.
Qed.

Lemma bindings_set_tree_collision_retains_representative :
  forall (K A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         fuel depth full_hash key (value : A) entries stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    NoDupA (fun left right => E (fst left) (fst right)) entries ->
    In (stored, old_value) entries ->
    E key stored ->
    In (stored, value)
      (bindings (set_tree eqb fuel depth full_hash key value
        (Collision full_hash entries))).
Proof.
  intros K A E eqb fuel depth full_hash key value entries stored old_value
    Hequiv Heqb Hnodup Hin Hrelated.
  rewrite set_tree_collision_same_hash, bindings_normalize_collision.
  eapply bucket_set_retains_representative; eauto.
Qed.

Lemma bindings_set_tree_retains_representative :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) fuel depth prefix full_hash
         (key : K) (value : A) (t : tree K A) stored (old_value : A),
    depth + fuel = branch_levels ->
    length prefix = depth ->
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second -> hash seed first = hash seed second) ->
    full_hash = hash seed key ->
    wf E hash seed depth prefix t ->
    In (stored, old_value) (bindings t) ->
    E key stored ->
    In (stored, value)
      (bindings (set_tree eqb fuel depth full_hash key value t)).
Proof.
  intros K Seed A E hash seed eqb fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash key value t stored
    old_value Hfuel Hlength Hequiv Heqb Hcongruent Hhash Hwf Hin Hrelated;
    destruct t as [|stored_hash leaf_key leaf_value|stored_hash entries|bitmap children].
  - contradiction.
  - simpl in Hin. destruct Hin as [Hin|[]].
    inversion Hin; subst stored old_value.
    cbn [set_tree]. rewrite (proj2 (Heqb key leaf_key) Hrelated). now left.
  - cbn [set_tree]. destruct (N.eqb full_hash stored_hash) eqn:Hsame.
    + rewrite bindings_normalize_collision.
      inversion Hwf as [| |d p hash' entries' Hentries Hmatches Hnodup|].
      eapply bucket_set_retains_representative; eauto.
    + exfalso.
      apply N.eqb_neq in Hsame. apply Hsame.
      inversion Hwf as [| |d p hash' entries' Hentries Hmatches Hnodup|].
      assert (Hentry : entry_matches hash seed stored_hash depth prefix
        (stored, old_value)).
      { apply (proj1 (Forall_forall
          (entry_matches hash seed stored_hash depth prefix) entries));
          assumption. }
      destruct Hentry as [Hstored_hash [_ _]].
      rewrite Hhash, Hstored_hash. now apply Hcongruent.
  - exfalso. eapply (@wf_branch_impossible_at_or_beyond_limit K Seed A E hash
      seed depth prefix bitmap children); [lia|exact Hwf].
  - contradiction.
  - simpl in Hin. destruct Hin as [Hin|[]].
    inversion Hin; subst stored old_value.
    cbn [set_tree]. rewrite (proj2 (Heqb key leaf_key) Hrelated). now left.
  - cbn [set_tree]. destruct (N.eqb full_hash stored_hash) eqn:Hsame.
    + rewrite bindings_normalize_collision.
      inversion Hwf as [| |d p hash' entries' Hentries Hmatches Hnodup|].
      eapply bucket_set_retains_representative; eauto.
    + exfalso.
      apply N.eqb_neq in Hsame. apply Hsame.
      inversion Hwf as [| |d p hash' entries' Hentries Hmatches Hnodup|].
      assert (Hentry : entry_matches hash seed stored_hash depth prefix
        (stored, old_value)).
      { apply (proj1 (Forall_forall
          (entry_matches hash seed stored_hash depth prefix) entries));
          assumption. }
      destruct Hentry as [Hstored_hash [_ _]].
      rewrite Hhash, Hstored_hash. now apply Hcongruent.
  - assert (Hstored_hash : hash seed stored = full_hash).
    { rewrite Hhash. now apply Hcongruent. }
    assert (Hpresent : bitmap_has bitmap (chunk full_hash depth) = true).
    { rewrite <- Hstored_hash.
      eapply (@wf_branch_binding_routes K Seed A E hash seed depth prefix
        bitmap children Hlength Hwf (stored, old_value) Hin). }
    destruct (wf_branch_ranked_child Hwf (chunk_bound full_hash depth) Hpresent)
      as [child [Hchild [_ Hchild_wf]]].
    assert (Hchild_in : In (stored, old_value) (bindings child)).
    { eapply (@wf_branch_dense_get_binding K Seed A E hash seed depth prefix
        bitmap children (chunk full_hash depth) child (stored, old_value)
        Hlength Hwf Hpresent Hchild Hin).
      simpl. now rewrite Hstored_hash. }
    assert (Hchild_updated : In (stored, value)
      (bindings (set_tree eqb fuel (S depth) full_hash key value child))).
    { eapply (IH (S depth) (prefix ++ [chunk full_hash depth]) full_hash key
        value child stored old_value).
      - lia.
      - rewrite app_length, Hlength. simpl. lia.
      - exact Hequiv.
      - exact Heqb.
      - exact Hcongruent.
      - exact Hhash.
      - exact Hchild_wf.
      - exact Hchild_in.
      - exact Hrelated. }
    rewrite (set_tree_branch_child eqb fuel depth full_hash key value bitmap
      children Hpresent Hchild).
    destruct (@bindings_dense_replace_split K A
      (rank bitmap (chunk full_hash depth))
      (set_tree eqb fuel (S depth) full_hash key value child) child children Hchild)
      as [before [after [Hbefore Hafter]]].
    simpl. rewrite Hafter. apply in_or_app. right. apply in_or_app. now left.
Qed.

Lemma elements_set_retains_representative :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A) (m : table K Seed A)
         stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    table_wf E hash m ->
    In (stored, old_value) (elements m) ->
    E key stored ->
    In (stored, value) (elements (set eqb hash key value m)).
Proof.
  intros K Seed A E hash eqb key value [seed root] stored old_value Hequiv Heqb
    Hcongruent Hwf Hin Hrelated.
  change (wf E hash seed 0 [] root) in Hwf.
  change (In (stored, old_value) (bindings root)) in Hin.
  change (In (stored, value)
    (bindings (set_tree eqb branch_levels 0 (hash seed key) key value root))).
  eapply (@bindings_set_tree_retains_representative K Seed A E hash seed eqb
    branch_levels 0 [] (hash seed key) key value root stored old_value); eauto.
Qed.

Lemma elements_set_other :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A) (m : table K Seed A)
         stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    ~ E stored key ->
    In (stored, old_value) (elements m) ->
    In (stored, old_value) (elements (set eqb hash key value m)).
Proof.
  intros K Seed A E hash eqb key value [seed root] stored old_value Hequiv Heqb
    Hother Hin.
  change (In (stored, old_value) (bindings root)) in Hin.
  change (In (stored, old_value)
    (bindings (set_tree eqb branch_levels 0 (hash seed key) key value root))).
  apply (proj2 (@bindings_set_tree_other K A E eqb branch_levels 0
    (hash seed key) key value root stored old_value Hequiv Heqb Hother)).
  exact Hin.
Qed.

Lemma elements_add_first_present :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (entries : list (K * A))
         (m : table K Seed A) stored (old_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    (forall key value, In (key, value) entries ->
      (hash (table_seed m) key < hash_space)%N) ->
    table_wf E hash m ->
    In (stored, old_value) (elements m) ->
    In (stored, old_value) (elements (add_first eqb hash entries m)).
Proof.
  intros K Seed A E hash eqb entries.
  induction entries as [|[key value] tail IH];
    intros m stored old_value Hequiv Heqb Hcongruent Hbound Hwf Hin.
  - exact Hin.
  - rewrite add_first_cons.
    destruct (get eqb hash key m) as [previous|] eqn:Hget.
    + eapply IH; eauto.
      intros key' value' Hin'. apply (Hbound key' value'). now right.
    + assert (Hother : ~ E stored key).
      { intro Hrelated.
        assert (Hkey_stored : E key stored).
        { destruct Hequiv as [_ Hsym _]. now apply Hsym. }
        pose proof (@get_binding_complete K Seed A E hash eqb key stored old_value m
          Hequiv Heqb Hcongruent
          (Hbound key value (or_introl eq_refl)) Hwf
          Hin Hkey_stored) as Hfound.
        rewrite Hget in Hfound. discriminate. }
      eapply IH with (m := set eqb hash key value m).
      * exact Hequiv.
      * exact Heqb.
      * exact Hcongruent.
      * intros key' value' Hin'. rewrite set_seed.
        apply (Hbound key' value'). now right.
      * eapply table_wf_set; eauto.
        apply (Hbound key value). now left.
      * eapply elements_set_other; eauto.
Qed.

Lemma elements_set_absent :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A) (m : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    (hash (table_seed m) key < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash key m = None ->
    In (key, value) (elements (set eqb hash key value m)).
Proof.
  intros K Seed A E hash eqb key value [seed root] Hequiv Heqb Hcongruent
    Hbound Hwf Hnone.
  assert (Hsetwf : table_wf E hash
    (set eqb hash key value {| table_seed := seed; table_root := root |})).
  { eapply table_wf_set; eauto. }
  assert (Hsetget : get eqb hash key
    (set eqb hash key value {| table_seed := seed; table_root := root |}) =
    Some value).
  { eapply get_after_set_self; eauto. }
  destruct (@get_binding_sound K Seed A E eqb hash key
    (set eqb hash key value {| table_seed := seed; table_root := root |}) value
    Heqb Hsetget) as [stored [Hstored Hrelated]].
  change (In (stored, value)
    (bindings (set_tree eqb branch_levels 0 (hash seed key) key value root)))
    in Hstored.
  destruct (@bindings_set_tree_key_origin K A eqb branch_levels 0 (hash seed key)
    key value root (stored, value) Hstored) as [[prior Hprior]|Hnew].
  - exfalso.
    pose proof (@get_binding_complete K Seed A E hash eqb key stored prior
      {| table_seed := seed; table_root := root |} Hequiv Heqb Hcongruent
      Hbound Hwf Hprior Hrelated) as Hfound.
    rewrite Hnone in Hfound. discriminate.
  - simpl in Hnew. subst stored. exact Hstored.
Qed.

Lemma elements_add_first_first_binding :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (entries : list (K * A))
         (m : table K Seed A) query stored (selected_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    (forall key value, In (key, value) entries ->
      (hash (table_seed m) key < hash_space)%N) ->
    (hash (table_seed m) query < hash_space)%N ->
    table_wf E hash m ->
    get eqb hash query m = None ->
    first_binding eqb query entries = Some (stored, selected_value) ->
    In (stored, selected_value) (elements (add_first eqb hash entries m)).
Proof.
  intros K Seed A E hash eqb entries.
  induction entries as [|[key value] tail IH];
    intros m query stored selected_value Hequiv Heqb Hcongruent Hbound
      Hquery_bound Hwf Hnone Hscan.
  - simpl in Hscan. discriminate.
  - simpl in Hscan. rewrite add_first_cons.
    destruct (eqb query key) eqn:Hquery_key.
    + inversion Hscan; subst stored selected_value.
      assert (Hkey_none : get eqb hash key m = None).
      { pose proof (@get_query_equiv K Seed A E eqb hash query key m
          Hequiv Heqb Hcongruent
          (proj1 (Heqb query key) Hquery_key)) as Hsame.
        rewrite Hnone in Hsame. now symmetry. }
      rewrite Hkey_none.
      eapply elements_add_first_present with (m := set eqb hash key value m).
      * exact Hequiv.
      * exact Heqb.
      * exact Hcongruent.
      * intros key' value' Hin. rewrite set_seed.
        apply (Hbound key' value'). now right.
      * eapply table_wf_set; eauto.
        apply (Hbound key value). now left.
      * eapply elements_set_absent; eauto.
        apply (Hbound key value). now left.
    + destruct (get eqb hash key m) as [previous|] eqn:Hkey.
      * eapply IH; eauto.
        intros key' value' Hin. apply (Hbound key' value'). now right.
      * assert (Hquery_none : get eqb hash query
          (set eqb hash key value m) = None).
        { rewrite (@get_after_set K Seed A E hash eqb query key value m
            Hequiv Heqb Hcongruent Hquery_bound
            (Hbound key value (or_introl eq_refl)) Hwf).
          now rewrite Hquery_key. }
        assert (Hbound_set : forall key' value', In (key', value') tail ->
          (hash (table_seed (set eqb hash key value m)) key' < hash_space)%N).
        { intros key' value' Hin. rewrite set_seed.
          apply (Hbound key' value'). now right. }
        assert (Hquery_bound_set :
          (hash (table_seed (set eqb hash key value m)) query < hash_space)%N).
        { rewrite set_seed. exact Hquery_bound. }
        assert (Hwf_set : table_wf E hash (set eqb hash key value m)).
        { eapply table_wf_set; eauto.
          apply (Hbound key value). now left. }
        exact (IH (set eqb hash key value m) query stored selected_value
          Hequiv Heqb Hcongruent Hbound_set Hquery_bound_set Hwf_set
          Hquery_none Hscan).
Qed.

Lemma elements_of_list_first_binding :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         query stored (selected_value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (hash seed query < hash_space)%N ->
    first_binding eqb query entries = Some (stored, selected_value) ->
    In (stored, selected_value) (elements (of_list eqb hash seed entries)).
Proof.
  intros K Seed A E hash seed eqb entries query stored selected_value Hequiv
    Heqb Hcongruent Hbound Hquery_bound Hscan.
  unfold of_list.
  eapply (@elements_add_first_first_binding K Seed A E hash eqb entries
    (empty seed) query stored selected_value Hequiv Heqb Hcongruent Hbound
    Hquery_bound (table_wf_empty E hash seed)).
  - apply get_empty.
  - exact Hscan.
Qed.

Lemma first_binding_some_eqb :
  forall (K A : Type) (eqb : K -> K -> bool) query
         (entries : list (K * A)) stored (value : A),
    first_binding eqb query entries = Some (stored, value) ->
    eqb query stored = true.
Proof.
  intros K A eqb query entries.
  induction entries as [|[key entry_value] tail IH]; intros stored value Hscan.
  - discriminate Hscan.
  - simpl in Hscan. destruct (eqb query key) eqn:Hkey.
    + inversion Hscan. subst stored value. exact Hkey.
    + eapply IH. exact Hscan.
Qed.

Lemma first_binding_some_in :
  forall (K A : Type) (eqb : K -> K -> bool) query
         (entries : list (K * A)) stored (value : A),
    first_binding eqb query entries = Some (stored, value) ->
    In (stored, value) entries.
Proof.
  intros K A eqb query entries.
  induction entries as [|[key entry_value] tail IH]; intros stored value Hscan.
  - discriminate Hscan.
  - simpl in Hscan. destruct (eqb query key) eqn:Hkey.
    + inversion Hscan. now left.
    + right. eapply IH. exact Hscan.
Qed.

Lemma NoDupA_related_in_eq :
  forall (K : Type) (E : K -> K -> Prop) (entries : list K) left right,
    Equivalence E ->
    NoDupA E entries ->
    In left entries ->
    In right entries ->
    E left right ->
    left = right.
Proof.
  intros K E entries.
  induction entries as [|head tail IH]; intros left right Hequiv Hnodup
    Hleft Hright Hrelated.
  - contradiction.
  - inversion Hnodup as [|head' tail' Hnotin Htail]; subst.
    simpl in Hleft, Hright.
    destruct Hleft as [Hleft|Hleft]; destruct Hright as [Hright|Hright].
    + now subst.
    + subst left. exfalso. apply Hnotin.
      apply (proj2 (InA_alt E head tail)).
      now exists right.
    + subst right. exfalso. apply Hnotin.
      apply (proj2 (InA_alt E head tail)).
      destruct Hequiv as [_ Hsym _]. now exists left.
    + eapply IH; eauto.
Qed.

Lemma elements_of_list_first_binding_converse :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         stored (value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    In (stored, value) (elements (of_list eqb hash seed entries)) ->
    first_binding eqb stored entries = Some (stored, value).
Proof.
  intros K Seed A E hash seed eqb entries stored value Hequiv Heqb Hcongruent
    Hentries Hin.
  assert (Hwf : table_wf E hash (of_list eqb hash seed entries)).
  { eapply table_wf_of_list; eauto. }
  assert (Hwf_root : wf E hash seed 0 []
    (table_root (of_list eqb hash seed entries))).
  { unfold table_wf in Hwf. rewrite of_list_seed in Hwf. exact Hwf. }
  change (In (stored, value)
    (bindings (table_root (of_list eqb hash seed entries)))) in Hin.
  destruct (@wf_binding_hash K Seed A E hash seed
    (table_root (of_list eqb hash seed entries)) 0 [] Hwf_root
    (stored, value) Hin) as [full_hash [Hhash Hbound]].
  assert (Hstored_bound : (hash seed stored < hash_space)%N).
  { simpl in Hhash. rewrite <- Hhash. exact Hbound. }
  assert (Hget : get eqb hash stored (of_list eqb hash seed entries) = Some value).
  { eapply (@get_binding_complete K Seed A E hash eqb stored stored value
      (of_list eqb hash seed entries)).
    - exact Hequiv.
    - exact Heqb.
    - exact Hcongruent.
    - rewrite of_list_seed. exact Hstored_bound.
    - exact Hwf.
    - exact Hin.
    - destruct Hequiv as [Href _ _]. apply Href. }
  pose proof (@get_of_list_first_binding K Seed A E hash seed eqb entries
    stored Hequiv Heqb Hcongruent Hentries Hstored_bound) as Hscan.
  rewrite Hget in Hscan.
  destruct (first_binding eqb stored entries) as [[selected selected_value]|]
    eqn:Hfirst; simpl in Hscan.
  - inversion Hscan. subst selected_value.
    assert (Hrelated : E stored selected).
    { apply (proj1 (Heqb stored selected)).
      eapply first_binding_some_eqb; eauto. }
    assert (Hselected : In (selected, value)
      (elements (of_list eqb hash seed entries))).
    { eapply (@elements_of_list_first_binding K Seed A E hash seed eqb entries
        stored selected value Hequiv Heqb Hcongruent Hentries).
      - exact Hstored_bound.
      - exact Hfirst. }
    assert (Hkeys : NoDupA E
      (map fst (elements (of_list eqb hash seed entries)))).
    { eapply of_list_elements_keys_nodup; eauto. }
    assert (Hstored_key : In stored
      (map fst (elements (of_list eqb hash seed entries)))).
    { apply in_map_iff. now exists (stored, value). }
    assert (Hselected_key : In selected
      (map fst (elements (of_list eqb hash seed entries)))).
    { apply in_map_iff. now exists (selected, value). }
    pose proof (@NoDupA_related_in_eq K E
      (map fst (elements (of_list eqb hash seed entries))) stored selected
      Hequiv Hkeys Hstored_key Hselected_key Hrelated) as Hkeys_equal.
    subst selected. reflexivity.
  - discriminate Hscan.
Qed.

Lemma elements_of_list_first_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         stored (value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (In (stored, value) (elements (of_list eqb hash seed entries)) <->
      first_binding eqb stored entries = Some (stored, value)).
Proof.
  intros K Seed A E hash seed eqb entries stored value Hequiv Heqb Hcongruent
    Hentries.
  split.
  - eapply elements_of_list_first_binding_converse; eauto.
  - intro Hscan.
    eapply (@elements_of_list_first_binding K Seed A E hash seed eqb entries
      stored stored value Hequiv Heqb Hcongruent Hentries).
    + apply (Hentries stored value).
      eapply (@first_binding_some_in K A eqb stored entries stored value).
      exact Hscan.
    + exact Hscan.
Qed.

Lemma first_binding_none_no_element :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (entries : list (K * A))
         query stored (value : A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    (hash seed query < hash_space)%N ->
    first_binding eqb query entries = None ->
    In (stored, value) (elements (of_list eqb hash seed entries)) ->
    ~ E query stored.
Proof.
  intros K Seed A E hash seed eqb entries query stored value Hequiv Heqb
    Hcongruent Hentries Hquery_bound Hscan Hin Hrelated.
  assert (Hwf : table_wf E hash (of_list eqb hash seed entries)).
  { eapply table_wf_of_list; eauto. }
  assert (Hget : get eqb hash query (of_list eqb hash seed entries) = None).
  { rewrite (@get_of_list_first_binding K Seed A E hash seed eqb entries
      query Hequiv Heqb Hcongruent Hentries Hquery_bound).
    now rewrite Hscan. }
  assert (Hquery_bound_map :
    (hash (table_seed (of_list eqb hash seed entries)) query < hash_space)%N).
  { rewrite of_list_seed. exact Hquery_bound. }
  pose proof (@get_binding_complete K Seed A E hash eqb query stored value
    (of_list eqb hash seed entries) Hequiv Heqb Hcongruent
    Hquery_bound_map Hwf Hin Hrelated) as Hfound.
  rewrite Hget in Hfound. discriminate.
Qed.

Lemma table_extensional_set :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) key (value : A) (left right : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    table_extensional eqb hash left right ->
    table_wf E hash left -> table_wf E hash right ->
    (hash (table_seed left) key < hash_space)%N ->
    (hash (table_seed right) key < hash_space)%N ->
    (forall query,
      (hash (table_seed left) query < hash_space)%N /\
      (hash (table_seed right) query < hash_space)%N) ->
    table_extensional eqb hash (set eqb hash key value left)
      (set eqb hash key value right).
Proof.
  intros K Seed A E hash eqb key value left right Hequiv Heqb Hcongruent Hext
    Hleft Hright Hkey_left Hkey_right Hbound query.
  destruct (Hbound query) as [Hquery_left Hquery_right].
  rewrite (@get_after_set K Seed A E hash eqb query key value left
    Hequiv Heqb Hcongruent Hquery_left Hkey_left Hleft).
  rewrite (@get_after_set K Seed A E hash eqb query key value right
    Hequiv Heqb Hcongruent Hquery_right Hkey_right Hright).
  now rewrite Hext.
Qed.

Lemma table_extensional_remove :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) key (left right : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    table_extensional eqb hash left right ->
    table_wf E hash left -> table_wf E hash right ->
    (forall query,
      (hash (table_seed left) query < hash_space)%N /\
      (hash (table_seed right) query < hash_space)%N) ->
    table_extensional eqb hash (remove eqb hash key left)
      (remove eqb hash key right).
Proof.
  intros K Seed A E hash eqb key left right Hequiv Heqb Hcongruent Hext
    Hleft Hright Hbound query.
  destruct (Hbound query) as [Hquery_left Hquery_right].
  rewrite (@get_after_remove K Seed A E hash eqb query key left
    Hequiv Heqb Hcongruent Hquery_left Hleft).
  rewrite (@get_after_remove K Seed A E hash eqb query key right
    Hequiv Heqb Hcongruent Hquery_right Hright).
  now rewrite Hext.
Qed.

Lemma table_extensional_mem :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (left right : table K Seed A),
    table_extensional eqb hash left right ->
    forall query,
      mem eqb hash query left = mem eqb hash query right.
Proof.
  intros K Seed A eqb hash left right Hext query.
  unfold mem. now rewrite Hext.
Qed.

Lemma table_extensional_is_empty :
  forall (K Seed A : Type) (E : K -> K -> Prop) (eqb : K -> K -> bool)
         (hash : Seed -> K -> N) (left right : table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second -> hash seed first = hash seed second) ->
    table_extensional eqb hash left right ->
    table_wf E hash left ->
    table_wf E hash right ->
    is_empty left = is_empty right.
Proof.
  intros K Seed A E eqb hash left right Hequiv Heqb Hcongruent Hext Hleft
    Hright.
  assert (Hempty : is_empty left = true <-> is_empty right = true).
  { split; intro Hempty.
    - apply (proj2 (@is_empty_iff_get_none K Seed A E eqb hash right Hequiv
        Heqb Hcongruent Hright)).
      intro query. rewrite <- Hext.
      apply (proj1 (@is_empty_iff_get_none K Seed A E eqb hash left Hequiv
        Heqb Hcongruent Hleft)).
      exact Hempty.
    - apply (proj2 (@is_empty_iff_get_none K Seed A E eqb hash left Hequiv
        Heqb Hcongruent Hleft)).
      intro query. rewrite Hext.
      apply (proj1 (@is_empty_iff_get_none K Seed A E eqb hash right Hequiv
        Heqb Hcongruent Hright)).
      exact Hempty. }
  destruct (is_empty left) eqn:Hleft_empty.
  - destruct (is_empty right) eqn:Hright_empty; [reflexivity|].
    exfalso.
    pose proof (proj1 Hempty eq_refl) as Hright_true.
    discriminate Hright_true.
  - destruct (is_empty right) eqn:Hright_empty; [|reflexivity].
    exfalso.
    pose proof (proj2 Hempty eq_refl) as Hleft_true.
    discriminate Hleft_true.
Qed.
