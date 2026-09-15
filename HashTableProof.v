(** Initial correctness lemmas for the executable HAMT source model.

    These base cases deliberately live outside [HashTable.v].  The recursive
    routing/invariant development can therefore build on stable operational
    equations without conflating specification and implementation. *)

From Stdlib Require Import Bool Lia List NArith SetoidList.
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

Lemma get_tree_zero_branch :
  forall (K A : Type) (eqb : K -> K -> bool) depth full_hash (key : K)
         bitmap (children : list (tree K A)),
    get_tree eqb 0 depth full_hash key (Branch bitmap children) = None.
Proof. reflexivity. Qed.

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

End LeafUpdateInvariant.

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

Lemma get_tree_collision_same_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash query
         (entries : list (K * A)),
    get_tree eqb fuel depth full_hash query (Collision full_hash entries) =
    bucket_get eqb query entries.
Proof. intros. destruct fuel; cbn [get_tree]; now rewrite N.eqb_refl. Qed.

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
