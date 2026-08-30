(** Focused certificates and refinement proof workspace for the specialized
    direct-string union worker. *)

From Stdlib Require Import PeanoNat Strings.String.
Require Import StringBits StringPatricia StringPatriciaProof StringPatriciaUnion.

Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros A left. destruct left; reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. reflexivity. Qed.

Theorem union_left_specialized_disjoint_samples:
  forall (A : Type) sample_a split (left_a right_a : t A)
      sample_b (left_b right_b : t A),
    agrees_before_bounded sample_a sample_b split = false ->
    union_left_specialized
      (Branch sample_a split left_a right_a)
      (Branch sample_b split left_b right_b) =
    join (Branch sample_a split left_a right_a)
      (Branch sample_b split left_b right_b).
Proof.
  intros A sample_a split left_a right_a sample_b left_b right_b Hagree.
  cbn [union_left_specialized]. rewrite Nat.eqb_refl, Hagree. reflexivity.
Qed.

(** Full contracts for the non-recursive leaf cases.  The remaining open
    refinement work is consequently confined to branch/branch routing. *)
Theorem union_left_specialized_leaf_left_correct_wf:
  forall (A : Type) key (value : A) (right : t A),
    wf right ->
    wf (union_left_specialized (Leaf key value) right) /\
    forall query,
      get query (union_left_specialized (Leaf key value) right) =
      match get query (Leaf key value) with
      | Some found => Some found
      | None => get query right
      end.
Proof.
  intros A key value right Hright.
  destruct right as [|right_key right_value|sample split left right].
  - split; [constructor|]. intro query.
    cbn [union_left_specialized get]. destruct (String.eqb query key); reflexivity.
  - rewrite union_left_specialized_equation.
    destruct (String.eqb key right_key) eqn:E.
    + apply String.eqb_eq in E. subst right_key.
      split; [constructor|]. intro query. cbn [get].
      destruct (String.eqb query key); reflexivity.
    + destruct (set_correct_wf A key value (Leaf right_key right_value) Hright)
        as [Hwf Hget].
      split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
      destruct (String.eqb query key); reflexivity.
  - destruct (set_correct_wf A key value (Branch sample split left right) Hright)
      as [Hwf Hget].
    split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
    destruct (String.eqb query key); reflexivity.
Qed.

Theorem union_left_specialized_leaf_right_correct_wf:
  forall (A : Type) (left : t A) key (value : A),
    wf left ->
    wf (union_left_specialized left (Leaf key value)) /\
    forall query,
      get query (union_left_specialized left (Leaf key value)) =
      match get query left with
      | Some found => Some found
      | None => get query (Leaf key value)
      end.
Proof.
  intros A left key value Hleft.
  destruct left as [|left_key left_value|sample split left right].
  - split; [constructor|]. intro query. cbn [union_left_specialized]. reflexivity.
  - rewrite union_left_specialized_equation.
    destruct (String.eqb left_key key) eqn:E.
    + apply String.eqb_eq in E. subst left_key.
      split; [constructor|]. intro query. cbn [get].
      destruct (String.eqb query key); reflexivity.
    + destruct (set_correct_wf A left_key left_value (Leaf key value)
        (wf_leaf key value)) as [Hwf Hget].
      split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
      destruct (String.eqb query left_key); reflexivity.
  - rewrite union_left_specialized_equation.
    destruct (get key (Branch sample split left right)) as [found|] eqn:E.
    + split; [exact Hleft|]. intro query.
      change (get query (Branch sample split left right) =
        match get query (Branch sample split left right) with
        | Some current => Some current
        | None => get query (Leaf key value)
        end).
      destruct (get query (Branch sample split left right)) as [current|] eqn:Q;
        [reflexivity|].
      destruct (String.eqb query key) eqn:K.
      * apply String.eqb_eq in K. subst query. rewrite E in Q. discriminate.
      * cbn [get]. now rewrite K.
    + destruct (set_correct_wf A key value (Branch sample split left right) Hleft)
        as [Hwf Hget].
      split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
      destruct (String.eqb query key) eqn:K.
      * apply String.eqb_eq in K. subst query.
        change (Some value =
          match get key (Branch sample split left right) with
          | Some current => Some current
          | None => Some value
          end).
        now rewrite E.
      * change (get query (Branch sample split left right) =
          match get query (Branch sample split left right) with
          | Some current => Some current
          | None => None
          end).
        destruct (get query (Branch sample split left right)); reflexivity.
Qed.

(** In the equal-split branch case, the cached samples may differ while still
    denoting the same prefix.  This lemma transfers the right tree onto the
    left sample and lifts each recursive biased-union contract back to the
    branch-side key invariant. *)
Lemma union_left_specialized_same_split_output_keys:
  forall (A : Type) sample_a sample_b split
      (left_a right_a left_b right_b out_left out_right : t A),
    agrees_before_bounded sample_a sample_b split = true ->
    all_keys (fun key =>
      same_prefix sample_a key split /\ bit_at key split = false) left_a ->
    all_keys (fun key =>
      same_prefix sample_a key split /\ bit_at key split = true) right_a ->
    all_keys (fun key =>
      same_prefix sample_b key split /\ bit_at key split = false) left_b ->
    all_keys (fun key =>
      same_prefix sample_b key split /\ bit_at key split = true) right_b ->
    wf out_left ->
    (forall key,
      get key out_left =
      match get key left_a with Some value => Some value | None => get key left_b end) ->
    wf out_right ->
    (forall key,
      get key out_right =
      match get key right_a with Some value => Some value | None => get key right_b end) ->
    all_keys (fun key =>
      same_prefix sample_a key split /\ bit_at key split = false) out_left /\
    all_keys (fun key =>
      same_prefix sample_a key split /\ bit_at key split = true) out_right.
Proof.
  intros A sample_a sample_b split left_a right_a left_b right_b out_left out_right
    Hagree Hla Hra Hlb Hrb Hwol Hgetol Hwor Hgetor.
  assert (Hprefix : same_prefix sample_a sample_b split).
  { unfold same_prefix. now apply (proj1
      (agrees_before_bounded_spec sample_a sample_b split)). }
  assert (Hlb' : all_keys (fun key =>
      same_prefix sample_a key split /\ bit_at key split = false) left_b).
  { eapply all_keys_equal_split_rebase; eauto. }
  assert (Hrb' : all_keys (fun key =>
      same_prefix sample_a key split /\ bit_at key split = true) right_b).
  { eapply all_keys_equal_split_rebase; eauto. }
  split.
  - eapply all_keys_of_combine_lookup with
      (left := left_a) (right := left_b) (out := out_left)
      (f := fun x y => match x with Some _ => x | None => y end).
    + reflexivity.
    + exact Hwol.
    + intro key. specialize (Hgetol key).
      destruct (get key left_a); cbn in Hgetol |- *; exact Hgetol.
    + exact Hla.
    + exact Hlb'.
  - eapply all_keys_of_combine_lookup with
      (left := right_a) (right := right_b) (out := out_right)
      (f := fun x y => match x with Some _ => x | None => y end).
    + reflexivity.
    + exact Hwor.
    + intro key. specialize (Hgetor key).
      destruct (get key right_a); cbn in Hgetor |- *; exact Hgetor.
    + exact Hra.
    + exact Hrb'.
Qed.

(** Complete reconstruction for equal split positions.  The worker retains
    the left cached sample, while [branch_wf_general] is free to rebase it to
    a resident output representative if either recursive result is empty. *)
Lemma union_left_specialized_same_branch_correct_wf:
  forall (A : Type) sample_a sample_b split
      (left_a right_a left_b right_b out_left out_right : t A),
    wf (Branch sample_a split left_a right_a) ->
    wf (Branch sample_b split left_b right_b) ->
    agrees_before_bounded sample_a sample_b split = true ->
    (wf out_left /\
      forall key,
        get key out_left =
        match get key left_a with Some value => Some value | None => get key left_b end) ->
    (wf out_right /\
      forall key,
        get key out_right =
        match get key right_a with Some value => Some value | None => get key right_b end) ->
    wf (branch sample_a split out_left out_right) /\
    forall key,
      get key (branch sample_a split out_left out_right) =
      match get key (Branch sample_a split left_a right_a) with
      | Some value => Some value
      | None => get key (Branch sample_b split left_b right_b)
      end.
Proof.
  intros A sample_a sample_b split left_a right_a left_b right_b out_left out_right
    Hwa Hwb Hagree [Hwol Hgetol] [Hwor Hgetor].
  inversion Hwa as [| |? ? ? ? Hwla Hwra _ _ Hla Hra _]; subst.
  inversion Hwb as [| |? ? ? ? Hwlb Hwrb _ _ Hlb Hrb _]; subst.
  destruct (union_left_specialized_same_split_output_keys A sample_a sample_b split
    left_a right_a left_b right_b out_left out_right Hagree
    Hla Hra Hlb Hrb Hwol Hgetol Hwor Hgetor) as [Houtl Houtr].
  split.
  - apply branch_wf_general; assumption.
  - intro key.
    assert (Houtlbit : all_keys (fun stored => bit_at stored split = false)
      out_left).
    { eapply all_keys_impl; [exact Houtl|]. intros stored H. exact (proj2 H). }
    assert (Houtrbit : all_keys (fun stored => bit_at stored split = true)
      out_right).
    { eapply all_keys_impl; [exact Houtr|]. intros stored H. exact (proj2 H). }
    rewrite (get_branch A sample_a split out_left out_right key Houtlbit Houtrbit).
    destruct (bit_at key split) eqn:E; cbn [get]; rewrite E.
    + apply Hgetor.
    + apply Hgetol.
Qed.
