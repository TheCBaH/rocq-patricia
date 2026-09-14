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

  Fixpoint prefix_matches (full_hash : N) (depth : nat) (prefix : list N) : Prop :=
    match prefix with
    | [] => True
    | slot :: rest =>
        chunk full_hash depth = slot /\ prefix_matches full_hash (S depth) rest
    end.

Lemma prefix_matches_append_slot :
    forall full_hash depth prefix slot,
      prefix_matches full_hash depth prefix ->
      chunk full_hash (depth + length prefix) = slot ->
      prefix_matches full_hash depth (prefix ++ [slot]).
  Proof.
    intros full_hash depth prefix. revert depth.
    induction prefix as [|head tail IH]; intros depth slot Hprefix Hslot.
    - simpl in Hprefix. simpl in Hslot.
      replace (depth + 0) with depth in Hslot by lia.
      simpl. split; [exact Hslot|exact I].
    - simpl in Hprefix. destruct Hprefix as [Hhead Htail]. simpl.
      split; auto.
      apply IH with (slot := slot); auto.
      replace (S depth + length tail) with (depth + S (length tail)) by lia.
      exact Hslot.
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
