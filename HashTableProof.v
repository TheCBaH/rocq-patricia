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

Lemma get_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) (eqb : K -> K -> bool) (key : K) (value : A)
         (t : tree K A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall first second, E first second ->
      hash seed first = hash seed second) ->
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
    Hequiv Heqb).
  - reflexivity.
  - intros first second Hrelated. apply Hcongruent. exact Hrelated.
  - exact Hbound.
  - exact Hwf.
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
