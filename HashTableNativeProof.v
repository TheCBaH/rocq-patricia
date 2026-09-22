(** Refinement theorems for the modeled compact-sequence backend.

    These theorems are about the Rocq [pseq] model.  They do not establish an
    OCaml array heap theorem; that remaining target obligation is recorded in
    the tracker. *)

From Stdlib Require Import Lia List NArith RelationClasses SetoidList.

Require Import HashTableSpec HashTable HashTableBits HashTableNativeBits HashTableNative HashTableProof.

Set Implicit Arguments.

Lemma native_get_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_get eqb fuel depth full_hash key native =
    get_tree eqb fuel depth full_hash key source.
Proof.
  intros K A eqb fuel depth full_hash key native source Hrefines.
  unfold native_refines in Hrefines. subst source.
  apply native_get_refines.
Qed.

Lemma native_set_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_refines (native_set eqb fuel depth full_hash key value native)
      (set_tree eqb fuel depth full_hash key value source).
Proof.
  intros K A eqb fuel depth full_hash key value native source Hrefines.
  unfold native_refines in *. subst source.
  apply native_set_refines.
Qed.

Lemma native_remove_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_refines (native_remove eqb fuel depth full_hash key native)
      (remove_tree eqb fuel depth full_hash key source).
Proof.
  intros K A eqb fuel depth full_hash key native source Hrefines.
  unfold native_refines in *. subst source.
  apply native_remove_refines.
Qed.

Definition native_table_wf {K Seed A : Type} (E : K -> K -> Prop)
    (hash : Seed -> K -> N) (native : native_table K Seed A) : Prop :=
  table_wf E hash (source_table_of_native native).

(** The scalar arguments reached by native lookup.  The property is stated
    over the transparent model so that it records the target binding domain
    without treating the OCaml realization as a Rocq function. *)
Fixpoint native_get_scalar_safe {K A : Type} (fuel depth : nat)
    (full_hash : N) (native : native_tree K A) : Prop :=
  (full_hash < hash_space)%N /\
  depth + fuel <= branch_levels /\
  match fuel, native with
  | S fuel', NativeBranch bitmap children =>
      (bitmap < bitmap_limit)%N /\
      match native_bitmap_has bitmap (native_chunk full_hash depth) with
      | true => forall child,
          pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = Some child ->
          native_get_scalar_safe fuel' (S depth) full_hash child
      | false => True
      end
  | _, _ => True
  end.

Lemma native_get_scalar_safe_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (native : native_tree K A),
    (full_hash < hash_space)%N ->
    depth + fuel <= branch_levels ->
    wf E hash seed depth prefix (source_of_native native) ->
    native_get_scalar_safe fuel depth full_hash native.
Proof.
  intros K Seed A E hash seed fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash native
    Hhash Hdepth Hwf.
  - destruct native; cbn [native_get_scalar_safe]; repeat split; try assumption; try lia; exact I.
  - destruct native as [|stored_hash stored value|stored_hash entries|bitmap children].
    + cbn [native_get_scalar_safe]. repeat split; try assumption; try lia; exact I.
    + cbn [native_get_scalar_safe]. repeat split; try assumption; try lia; exact I.
    + cbn [native_get_scalar_safe]. repeat split; try assumption; try lia; exact I.
    + cbn [native_get_scalar_safe source_of_native].
      split; [exact Hhash|]. split; [exact Hdepth|].
      inversion Hwf as [| | |actual_depth actual_prefix actual_bitmap actual_children
        Hbranch_depth Hbitmap _ _ Hchildren _];
        subst actual_depth actual_prefix actual_bitmap actual_children.
      split; [exact Hbitmap|].
      destruct (native_bitmap_has bitmap (native_chunk full_hash depth)) eqn:Hpresent; [|exact I].
      intros child Hchild.
      change (bitmap_has bitmap (chunk full_hash depth) = true) in Hpresent.
      pose proof (@pseq_get_source_children K A
        (rank bitmap (chunk full_hash depth)) children child Hchild) as Hsource.
      destruct (@wf_branch_ranked_child K Seed A E hash seed depth prefix bitmap
        (map source_of_native (pseq_view children)) (chunk full_hash depth)
        Hwf (chunk_bound full_hash depth) Hpresent)
        as [source_child [Hindexed [_ Hchildwf]]].
      rewrite Hsource in Hindexed. inversion Hindexed. subst source_child.
      apply (IH (S depth) (prefix ++ chunk full_hash depth :: nil) full_hash child);
        try assumption; lia.
Qed.

Lemma native_table_get_scalar_safe :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (query : K) (native : native_table K Seed A),
    (hash (native_table_seed native) query < hash_space)%N ->
    native_table_wf E hash native ->
    native_get_scalar_safe branch_levels 0
      (hash (native_table_seed native) query) (native_table_root native).
Proof.
  intros K Seed A E hash query native Hhash Hwf.
  destruct native as [seed root].
  unfold native_table_wf, table_wf, source_table_of_native in Hwf.
  apply (@native_get_scalar_safe_wf K Seed A E hash seed branch_levels 0 nil
    (hash seed query) root); try assumption.
  cbv [branch_levels]. lia.
Qed.

(** Direct joins use scalar chunks at each remaining routing depth. *)
Fixpoint native_join_scalar_safe (fuel depth : nat) (left_hash right_hash : N) : Prop :=
  (left_hash < hash_space)%N /\
  (right_hash < hash_space)%N /\
  depth + fuel <= branch_levels /\
  match fuel with
  | O => True
  | S fuel' => native_join_scalar_safe fuel' (S depth) left_hash right_hash
  end.

Lemma native_join_scalar_safe_of_bounds :
  forall fuel depth left_hash right_hash,
    (left_hash < hash_space)%N ->
    (right_hash < hash_space)%N ->
    depth + fuel <= branch_levels ->
    native_join_scalar_safe fuel depth left_hash right_hash.
Proof.
  induction fuel as [|fuel IH]; intros depth left_hash right_hash Hleft Hright Hdepth;
    cbn [native_join_scalar_safe]; repeat split; try assumption; try lia; try exact I.
  apply IH; try assumption; lia.
Qed.

(** Update traversals share branch routing with lookup, and may additionally
    invoke a direct join at a leaf or collision.  This stronger invariant
    records both classes of scalar call without assuming that the target
    realization is a Rocq function. *)
Fixpoint native_update_scalar_safe {K A : Type} (fuel depth : nat)
    (full_hash : N) (native : native_tree K A) : Prop :=
  (full_hash < hash_space)%N /\
  depth + fuel <= branch_levels /\
  match fuel, native with
  | S fuel', NativeBranch bitmap children =>
      (bitmap < bitmap_limit)%N /\
      match native_bitmap_has bitmap (native_chunk full_hash depth) with
      | true => forall child,
          pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = Some child ->
          native_update_scalar_safe fuel' (S depth) full_hash child
      | false => True
      end
  | _, NativeLeaf stored_hash _ _ =>
      native_join_scalar_safe fuel depth full_hash stored_hash
  | _, NativeCollision stored_hash _ =>
      native_join_scalar_safe fuel depth full_hash stored_hash
  | _, _ => True
  end.

Lemma native_update_scalar_safe_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (seed : Seed) fuel depth prefix full_hash (native : native_tree K A),
    (full_hash < hash_space)%N ->
    depth + fuel <= branch_levels ->
    wf E hash seed depth prefix (source_of_native native) ->
    native_update_scalar_safe fuel depth full_hash native.
Proof.
  intros K Seed A E hash seed fuel.
  induction fuel as [|fuel IH]; intros depth prefix full_hash native
    Hhash Hdepth Hwf.
  - destruct native as [|stored_hash stored value|stored_hash entries|bitmap children].
    + cbn [native_update_scalar_safe]. repeat split; try assumption; try lia; exact I.
    + cbn [native_update_scalar_safe source_of_native] in *.
      split; [exact Hhash|]. split; [exact Hdepth|].
      inversion Hwf; subst. now apply native_join_scalar_safe_of_bounds.
    + cbn [native_update_scalar_safe source_of_native] in *.
      split; [exact Hhash|]. split; [exact Hdepth|].
      apply native_join_scalar_safe_of_bounds; try assumption.
      eapply (@wf_collision_hash_bound K Seed A E hash seed depth prefix stored_hash
        (pseq_view entries)); exact Hwf.
    + cbn [native_update_scalar_safe]. repeat split; try assumption; try lia; exact I.
  - destruct native as [|stored_hash stored value|stored_hash entries|bitmap children].
    + cbn [native_update_scalar_safe]. repeat split; try assumption; try lia; exact I.
    + cbn [native_update_scalar_safe source_of_native] in *.
      split; [exact Hhash|]. split; [exact Hdepth|].
      inversion Hwf; subst. now apply native_join_scalar_safe_of_bounds.
    + cbn [native_update_scalar_safe source_of_native] in *.
      split; [exact Hhash|]. split; [exact Hdepth|].
      apply native_join_scalar_safe_of_bounds; try assumption.
      eapply (@wf_collision_hash_bound K Seed A E hash seed depth prefix stored_hash
        (pseq_view entries)); exact Hwf.
    + cbn [native_update_scalar_safe source_of_native].
      split; [exact Hhash|]. split; [exact Hdepth|].
      inversion Hwf as [| | |actual_depth actual_prefix actual_bitmap actual_children
        Hbranch_depth Hbitmap _ _ Hchildren _];
        subst actual_depth actual_prefix actual_bitmap actual_children.
      split; [exact Hbitmap|].
      destruct (native_bitmap_has bitmap (native_chunk full_hash depth)) eqn:Hpresent; [|exact I].
      intros child Hchild.
      change (bitmap_has bitmap (chunk full_hash depth) = true) in Hpresent.
      pose proof (@pseq_get_source_children K A
        (rank bitmap (chunk full_hash depth)) children child Hchild) as Hsource.
      destruct (@wf_branch_ranked_child K Seed A E hash seed depth prefix bitmap
        (map source_of_native (pseq_view children)) (chunk full_hash depth)
        Hwf (chunk_bound full_hash depth) Hpresent)
        as [source_child [Hindexed [_ Hchildwf]]].
      rewrite Hsource in Hindexed. inversion Hindexed. subst source_child.
      apply (IH (S depth) (prefix ++ chunk full_hash depth :: nil) full_hash child);
        try assumption; lia.
Qed.

Lemma native_table_update_scalar_safe :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (query : K) (native : native_table K Seed A),
    (hash (native_table_seed native) query < hash_space)%N ->
    native_table_wf E hash native ->
    native_update_scalar_safe branch_levels 0
      (hash (native_table_seed native) query) (native_table_root native).
Proof.
  intros K Seed A E hash query native Hhash Hwf.
  destruct native as [seed root].
  unfold native_table_wf, table_wf, source_table_of_native in Hwf.
  apply (@native_update_scalar_safe_wf K Seed A E hash seed branch_levels 0 nil
    (hash seed query) root); try assumption.
  cbv [branch_levels]. lia.
Qed.

Lemma native_table_set_scalar_safe :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (key : K) (value : A) (native : native_table K Seed A),
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_update_scalar_safe branch_levels 0
      (hash (native_table_seed native) key) (native_table_root native).
Proof.
  intros K Seed A E hash key value native Hhash Hwf.
  eapply (@native_table_update_scalar_safe K Seed A E hash key native); eauto.
Qed.

Lemma native_table_remove_scalar_safe :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (key : K) (native : native_table K Seed A),
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_update_scalar_safe branch_levels 0
      (hash (native_table_seed native) key) (native_table_root native).
Proof.
  intros K Seed A E hash key native Hhash Hwf.
  eapply (@native_table_update_scalar_safe K Seed A E hash key native); eauto.
Qed.

(** A first-wins load invokes lookup first and only invokes set on absence.
    This trace property retains the domain fact for every such call. *)
Fixpoint native_table_add_first_scalar_safe {K Seed A : Type}
    (eqb : K -> K -> bool) (hash : Seed -> K -> N)
    (entries : list (K * A)) (native : native_table K Seed A) : Prop :=
  match entries with
  | nil => True
  | (key, value) :: tail =>
      native_get_scalar_safe branch_levels 0
        (hash (native_table_seed native) key) (native_table_root native) /\
      match native_table_get eqb hash key native with
      | Some _ => native_table_add_first_scalar_safe eqb hash tail native
      | None =>
          native_update_scalar_safe branch_levels 0
            (hash (native_table_seed native) key) (native_table_root native) /\
          native_table_add_first_scalar_safe eqb hash tail
            (native_table_set eqb hash key value native)
      end
  end.

Lemma native_table_add_first_scalar_safe_wf :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (entries : list (K * A))
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (forall key value, In (key, value) entries ->
      (hash (native_table_seed native) key < hash_space)%N) ->
    native_table_wf E hash native ->
    native_table_add_first_scalar_safe eqb hash entries native.
Proof.
  intros K Seed A E hash eqb entries.
  induction entries as [|[key value] tail IH]; intros native Hequiv Heqb Hcongruent
    Hbound Hwf; cbn [native_table_add_first_scalar_safe].
  - exact I.
  - assert (Hkey : (hash (native_table_seed native) key < hash_space)%N).
    { apply (Hbound key value). now left. }
    split.
    + eapply native_table_get_scalar_safe; eauto.
    + destruct (native_table_get eqb hash key native) eqn:Hget.
      * apply IH; try assumption.
        intros key' value' Hin. apply (Hbound key' value'). now right.
      * split.
        -- eapply native_table_set_scalar_safe; eauto.
        -- apply IH.
           ++ exact Hequiv.
           ++ exact Heqb.
           ++ exact Hcongruent.
           ++ intros key' value' Hin.
              rewrite native_table_set_seed.
              apply (Hbound key' value'). now right.
           ++ unfold native_table_wf.
              change (table_wf E hash (source_table_of_native native)) in Hwf.
              change (table_wf E hash
                (source_table_of_native (native_table_set eqb hash key value native))).
              rewrite source_table_native_set.
              eapply table_wf_set; eauto.
Qed.

Lemma native_table_of_list_scalar_safe :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (seed : Seed) (entries : list (K * A)),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall actual_seed first second, E first second ->
      hash actual_seed first = hash actual_seed second) ->
    (forall key value, In (key, value) entries ->
      (hash seed key < hash_space)%N) ->
    native_table_add_first_scalar_safe eqb hash entries (native_empty seed).
Proof.
  intros K Seed A E hash eqb seed entries Hequiv Heqb Hcongruent Hbound.
  eapply native_table_add_first_scalar_safe_wf; eauto.
  unfold native_table_wf. rewrite source_table_native_empty.
  apply table_wf_empty.
Qed.

Lemma native_table_wf_empty :
  forall K Seed A (E : K -> K -> Prop) (hash : Seed -> K -> N) (seed : Seed),
    native_table_wf E hash (@native_empty K Seed A seed).
Proof.
  intros. unfold native_table_wf. rewrite source_table_native_empty.
  apply table_wf_empty.
Qed.

Lemma native_table_wf_set :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_wf E hash (native_table_set eqb hash key value native).
Proof.
  intros K Seed A E hash eqb key value native Hequiv Heqb Hcongruent Hbound Hwf.
  change (table_wf E hash (source_table_of_native native)) in Hwf.
  change (table_wf E hash
    (source_table_of_native (native_table_set eqb hash key value native))).
  rewrite source_table_native_set.
  eapply table_wf_set; eauto.
Qed.

Lemma native_table_wf_remove :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    native_table_wf E hash (native_table_remove eqb hash key native).
Proof.
  intros K Seed A E hash eqb key native Hequiv Heqb Hcongruent Hwf.
  change (table_wf E hash (source_table_of_native native)) in Hwf.
  change (table_wf E hash
    (source_table_of_native (native_table_remove eqb hash key native))).
  rewrite source_table_native_remove.
  eapply table_wf_remove; eauto.
Qed.

Lemma native_table_get_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_get eqb hash key (native_table_set eqb hash key value native) =
    Some value.
Proof.
  intros K Seed A E hash eqb key value native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_get_refines, source_table_native_set.
  eapply get_after_set_self; eauto.
Qed.

Lemma native_table_mem_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_mem eqb hash key (native_table_set eqb hash key value native) = true.
Proof.
  intros K Seed A E hash eqb key value native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_mem_refines, source_table_native_set.
  eapply mem_after_set_self; eauto.
Qed.

Lemma native_table_get_after_remove_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    native_table_get eqb hash key (native_table_remove eqb hash key native) = None.
Proof.
  intros K Seed A E hash eqb key native Hequiv Heqb Hcongruent Hwf.
  rewrite native_table_get_refines, source_table_native_remove.
  eapply get_after_remove_self; eauto.
Qed.

Lemma native_table_mem_after_remove_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    native_table_mem eqb hash key (native_table_remove eqb hash key native) = false.
Proof.
  intros K Seed A E hash eqb key native Hequiv Heqb Hcongruent Hwf.
  rewrite native_table_mem_refines, source_table_native_remove.
  eapply mem_after_remove_self; eauto.
Qed.

Lemma native_table_get_after_set_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_get eqb hash query (native_table_set eqb hash key value native) =
    Some value.
Proof.
  intros K Seed A E hash eqb query key value native Hequiv Heqb Hcongruent
    Hrelated Hbound Hwf.
  rewrite native_table_get_refines, source_table_native_set.
  eapply get_after_set_equiv; eauto.
Qed.

Lemma native_table_mem_after_set_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_mem eqb hash query (native_table_set eqb hash key value native) = true.
Proof.
  intros K Seed A E hash eqb query key value native Hequiv Heqb Hcongruent
    Hrelated Hbound Hwf.
  rewrite native_table_mem_refines, source_table_native_set.
  eapply mem_after_set_equiv; eauto.
Qed.

Lemma native_table_get_after_remove_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    native_table_wf E hash native ->
    native_table_get eqb hash query (native_table_remove eqb hash key native) = None.
Proof.
  intros K Seed A E hash eqb query key native Hequiv Heqb Hcongruent Hrelated Hwf.
  rewrite native_table_get_refines, source_table_native_remove.
  eapply get_after_remove_equiv; eauto.
Qed.

Lemma native_table_mem_after_remove_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    native_table_wf E hash native ->
    native_table_mem eqb hash query (native_table_remove eqb hash key native) = false.
Proof.
  intros K Seed A E hash eqb query key native Hequiv Heqb Hcongruent Hrelated Hwf.
  rewrite native_table_mem_refines, source_table_native_remove.
  eapply mem_after_remove_equiv; eauto.
Qed.

Lemma native_table_get_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) query < hash_space)%N ->
    native_table_wf E hash native ->
    (native_table_get eqb hash query native = Some value <->
      exists stored,
        In (stored, value) (native_table_elements native) /\ E query stored).
Proof.
  intros K Seed A E hash eqb query value native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_get_refines, native_table_elements_refines.
  eapply get_binding_iff; eauto.
Qed.

Lemma native_table_mem_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) query < hash_space)%N ->
    native_table_wf E hash native ->
    (native_table_mem eqb hash query native = true <->
      exists stored value,
        In (stored, value) (native_table_elements native) /\ E query stored).
Proof.
  intros K Seed A E hash eqb query native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_mem_refines, native_table_elements_refines.
  eapply mem_binding_iff; eauto.
Qed.

Lemma native_table_elements_keys_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (native : native_table K Seed A),
    native_table_wf E hash native ->
    NoDupA E (map fst (native_table_elements native)).
Proof.
  intros K Seed A E hash native Hwf.
  rewrite native_table_elements_refines.
  apply (@elements_keys_nodup K Seed A E hash (source_table_of_native native)).
  exact Hwf.
Qed.

Lemma native_table_is_empty_iff_get_none :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    (native_table_is_empty native = true <->
      forall query, native_table_get eqb hash query native = None).
Proof.
  intros K Seed A E hash eqb native Hequiv Heqb Hcongruent Hwf.
  rewrite native_table_is_empty_refines.
  rewrite (@is_empty_iff_get_none K Seed A E eqb hash
    (source_table_of_native native) Hequiv Heqb Hcongruent Hwf).
  split; intros Hall query.
  - rewrite native_table_get_refines. apply Hall.
  - rewrite <- native_table_get_refines. apply Hall.
Qed.
