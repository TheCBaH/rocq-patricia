(** Focused certificates and refinement proof workspace for the specialized
    direct-string union worker. *)

From Stdlib Require Import Arith.Wf_nat Lia PeanoNat Strings.String.
Require Import StringBits StringPatricia StringPatriciaProof StringPatriciaUnion.

Definition nonempty {A : Type} (tree : t A) : Prop :=
  exists key value, get key tree = Some value.

Lemma set_nonempty_unconditional:
  forall (A : Type) key (value : A) (tree : t A),
    wf tree ->
    nonempty (set key value tree).
Proof.
  intros A key value tree Hwf. exists key, value. apply get_set_same; exact Hwf.
Qed.

Lemma changed_result_nonempty:
  forall (A : Type) (original changed : t A),
    nonempty changed ->
    reuse_changed original changed = changed.
Proof.
  intros A original changed Hnonempty.
  unfold reuse_changed.
  destruct changed as [|key value|sample split left right].
  - destruct Hnonempty as [key [value Hget]]. discriminate.
  - reflexivity.
  - reflexivity.
Qed.

(** The semantic contract required of OCaml physical equality. A false
    negative only rebuilds a branch, so the proof needs soundness in the
    positive direction only. *)
Definition native_same_sound {A : Type} (same : t A -> t A -> bool) : Prop :=
  forall changed original,
    same changed original = true -> equiv changed original.

Lemma native_reuse_child_correct_wf:
  forall (A : Type) (same : t A -> t A -> bool) (original right changed : t A),
    native_same_sound same ->
    wf original -> wf changed ->
    (forall key,
      get key changed =
      match get key original with Some value => Some value | None => get key right end) ->
    wf (native_reuse_child same original changed) /\
    forall key,
      get key (native_reuse_child same original changed) =
      match get key original with Some value => Some value | None => get key right end.
Proof.
  intros A same original right changed Hsame Hwor Hwch Hget.
  unfold native_reuse_child. destruct (same changed original) eqn:Esame.
  - split; [exact Hwor|]. intro key.
    rewrite <- (Hsame changed original Esame key) at 1. apply Hget.
  - split; [exact Hwch|exact Hget].
Qed.

Lemma biased_output_nonempty_left:
  forall (A : Type) (left right out : t A),
    nonempty left ->
    (forall key,
      get key out =
      match get key left with Some value => Some value | None => get key right end) ->
    nonempty out.
Proof.
  intros A left right out [key [value Hget]] Hout.
  exists key, value. rewrite Hout, Hget. reflexivity.
Qed.

Lemma reuse_changed_correct_nonempty_left:
  forall (A : Type) (original changed left right : t A),
    nonempty left ->
    (wf changed /\
      forall key,
        get key changed =
        match get key left with Some value => Some value | None => get key right end) ->
    wf (reuse_changed original changed) /\
    forall key,
      get key (reuse_changed original changed) =
      match get key left with Some value => Some value | None => get key right end.
Proof.
  intros A original changed left right Hleft Hcorrect.
  assert (Hchanged : nonempty changed).
  { eapply biased_output_nonempty_left; [exact Hleft|exact (proj2 Hcorrect)]. }
  rewrite changed_result_nonempty by exact Hchanged. exact Hcorrect.
Qed.

Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros A left. destruct left; reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. reflexivity. Qed.

(** The changed worker agrees with the original worker in all non-recursive
    shapes.  These bridge lemmas keep the branch/branch proof focused on
    reconstruction. *)
Lemma union_left_specialized_changed_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized_changed_result Empty right =
    union_left_specialized Empty right.
Proof. intros A right. destruct right; reflexivity. Qed.

Lemma union_left_specialized_changed_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized_changed_result left Empty =
    union_left_specialized left Empty.
Proof. intros A left. destruct left; reflexivity. Qed.

Lemma union_left_specialized_changed_leaf_left:
  forall (A : Type) key (value : A) (right : t A),
    wf right ->
    union_left_specialized_changed_result (Leaf key value) right =
    union_left_specialized (Leaf key value) right.
Proof.
  intros A key value right Hright. destruct right as [|stored stored_value|sample split l r].
  - reflexivity.
  - destruct (String.eqb key stored) eqn:Eequal.
    + unfold union_left_specialized_changed_result.
      rewrite union_left_specialized_changed_equation, Eequal.
      rewrite union_left_specialized_equation, Eequal. reflexivity.
    + unfold union_left_specialized_changed_result.
      rewrite union_left_specialized_changed_equation, Eequal.
      rewrite union_left_specialized_equation, Eequal.
      apply changed_result_nonempty. apply set_nonempty_unconditional; exact Hright.
  - unfold union_left_specialized_changed_result.
    rewrite union_left_specialized_changed_equation.
    rewrite union_left_specialized_equation.
    apply changed_result_nonempty. apply set_nonempty_unconditional; exact Hright.
Qed.

Lemma union_left_specialized_changed_leaf_right:
  forall (A : Type) (left : t A) key (value : A),
    wf left ->
    union_left_specialized_changed_result left (Leaf key value) =
    union_left_specialized left (Leaf key value).
Proof.
  intros A left key value Hleft. destruct left as [|stored stored_value|sample split l r].
  - reflexivity.
  - destruct (String.eqb stored key) eqn:Eequal.
    + unfold union_left_specialized_changed_result.
      rewrite union_left_specialized_changed_equation, Eequal.
      rewrite union_left_specialized_equation, Eequal. reflexivity.
    + unfold union_left_specialized_changed_result.
      rewrite union_left_specialized_changed_equation, Eequal.
      rewrite union_left_specialized_equation, Eequal.
      apply changed_result_nonempty. apply set_nonempty_unconditional; constructor.
  - unfold union_left_specialized_changed_result.
    rewrite union_left_specialized_changed_equation.
    rewrite union_left_specialized_equation.
    destruct (get key (Branch sample split l r)); [reflexivity|].
    apply changed_result_nonempty. apply set_nonempty_unconditional; exact Hleft.
Qed.

(** Smart branches may refresh their cached sample, but lookup ignores that
    field.  With nonempty children, refreshing it cannot collapse the branch. *)
Lemma get_branch_cached_sample_irrelevant:
  forall (A : Type) sample split (left right : t A) key,
    representative left <> None -> representative right <> None ->
    get key (branch sample split left right) =
    get key (Branch sample split left right).
Proof.
  intros A sample split left right key Hleft Hright.
  unfold branch.
  destruct left as [|left_key left_value|left_sample left_split left_left left_right].
  - exfalso. apply Hleft. reflexivity.
  - destruct right as [|right_key right_value|right_sample right_split right_left right_right].
    + exfalso. apply Hright. reflexivity.
    + reflexivity.
    + reflexivity.
  - destruct right as [|right_key right_value|right_sample right_split right_left right_right].
    + exfalso. apply Hright. reflexivity.
    + cbn [representative]. destruct (representative left_left);
        [cbn [get]; reflexivity|].
      destruct (representative left_right); cbn [get]; reflexivity.
    + cbn [representative]. destruct (representative left_left);
        [cbn [get]; reflexivity|].
      destruct (representative left_right); cbn [get]; reflexivity.
Qed.

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

(** Cached samples add one obligation to the native equal-header fragment:
    the original sample must remain resident after a sound child replacement.
    Left bias supplies that fact, so no stronger property of [same] is needed. *)
Lemma native_reuse_same_branch_correct_wf:
  forall (A : Type) (same : t A -> t A -> bool) sample_a sample_b split
      (left_a right_a left_b right_b out_left out_right : t A),
    native_same_sound same ->
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
    wf (native_reuse_same_branch same sample_a split
      left_a right_a out_left out_right) /\
    forall key,
      get key (native_reuse_same_branch same sample_a split
        left_a right_a out_left out_right) =
      match get key (Branch sample_a split left_a right_a) with
      | Some value => Some value
      | None => get key (Branch sample_b split left_b right_b)
      end.
Proof.
  intros A same sample_a sample_b split left_a right_a left_b right_b out_left out_right
    Hsame Hwa Hwb Hagree Hleft Hright.
  inversion Hwa as
      [| |? ? ? ? Hwla Hwra Hnla Hnra Hla Hra Hresidenta]; subst.
  inversion Hwb as
      [| |? ? ? ? Hwlb Hwrb Hnlb Hnrb Hlb Hrb Hresidentb]; subst.
  destruct (native_reuse_child_correct_wf A same left_a left_b out_left
    Hsame Hwla (proj1 Hleft) (proj2 Hleft)) as [Hwol Hgetol].
  destruct (native_reuse_child_correct_wf A same right_a right_b out_right
    Hsame Hwra (proj1 Hright) (proj2 Hright)) as [Hwor Hgetor].
  destruct (union_left_specialized_same_split_output_keys A sample_a sample_b split
    left_a right_a left_b right_b
    (native_reuse_child same left_a out_left)
    (native_reuse_child same right_a out_right)
    Hagree Hla Hra Hlb Hrb Hwol Hgetol Hwor Hgetor) as [Houtl Houtr].
  split.
  - unfold native_reuse_same_branch. apply wf_branch.
    + exact Hwol.
    + exact Hwor.
    + destruct (representative left_a) as [key|] eqn:Eleft.
      * destruct (representative_resident_wf A left_a key Hwla Eleft)
          as [value Hget].
        eapply wf_representative_nonempty_get; [exact Hwol|].
        rewrite Hgetol, Hget. reflexivity.
      * exfalso. exact (Hnla eq_refl).
    + destruct (representative right_a) as [key|] eqn:Eright.
      * destruct (representative_resident_wf A right_a key Hwra Eright)
          as [value Hget].
        eapply wf_representative_nonempty_get; [exact Hwor|].
        rewrite Hgetor, Hget. reflexivity.
      * exfalso. exact (Hnra eq_refl).
    + exact Houtl.
    + exact Houtr.
    + destruct Hresidenta as [value Hget]. exists value.
      destruct (bit_at sample_a split) eqn:Ebit;
        cbn [get] in Hget |- *; rewrite Ebit in Hget |- *.
      * rewrite Hgetor, Hget. reflexivity.
      * rewrite Hgetol, Hget. reflexivity.
  - intro key. unfold native_reuse_same_branch.
    destruct (bit_at key split) eqn:Ebit;
      cbn [get]; rewrite Ebit; [rewrite Hgetor|rewrite Hgetol]; reflexivity.
Qed.

Lemma union_left_specialized_changed_same_branch_correct_wf:
  forall (A : Type) sample_a sample_b split
      (left_a right_a left_b right_b : t A),
    wf (Branch sample_a split left_a right_a) ->
    wf (Branch sample_b split left_b right_b) ->
    agrees_before_bounded sample_a sample_b split = true ->
    (wf (union_left_specialized_changed_result left_a left_b) /\
      forall key,
        get key (union_left_specialized_changed_result left_a left_b) =
        match get key left_a with Some value => Some value | None => get key left_b end) ->
    (wf (union_left_specialized_changed_result right_a right_b) /\
      forall key,
        get key (union_left_specialized_changed_result right_a right_b) =
        match get key right_a with Some value => Some value | None => get key right_b end) ->
    wf (union_left_specialized_changed_result
      (Branch sample_a split left_a right_a)
      (Branch sample_b split left_b right_b)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch sample_a split left_a right_a)
        (Branch sample_b split left_b right_b)) =
      match get key (Branch sample_a split left_a right_a) with
      | Some value => Some value
      | None => get key (Branch sample_b split left_b right_b)
      end.
Proof.
  intros A sample_a sample_b split left_a right_a left_b right_b
    Hwa Hwb Hagree Hleft Hright.
  inversion Hwa as [| |? ? ? ? Hwla Hwra Hnla Hnra Hla Hra Hresidenta]; subst.
  inversion Hwb as [| |? ? ? ? Hwlb Hwrb Hnlb Hnrb Hlb Hrb Hresidentb]; subst.
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  cbn -[branch reuse_changed]. rewrite Nat.eqb_refl, Hagree.
  destruct (union_left_specialized_changed left_a left_b) eqn:Eleft;
    destruct (union_left_specialized_changed right_a right_b) eqn:Eright.
  - unfold union_left_specialized_changed_result in Hleft, Hright.
    rewrite Eleft in Hleft. rewrite Eright in Hright.
    destruct (union_left_specialized_same_branch_correct_wf A sample_a sample_b split
      left_a right_a left_b right_b left_a right_a Hwa Hwb Hagree Hleft Hright)
      as [_ Hget].
    split; [exact Hwa|]. intro key.
    change (get key (Branch sample_a split left_a right_a) =
      match get key (Branch sample_a split left_a right_a) with
      | Some value => Some value
      | None => get key (Branch sample_b split left_b right_b)
      end).
    rewrite <- (get_branch_cached_sample_irrelevant A sample_a split left_a right_a key
      Hnla Hnra) at 1.
    apply Hget.
  Local Ltac solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta :=
    unfold union_left_specialized_changed_result in Hleft, Hright;
    rewrite Eleft in Hleft; rewrite Eright in Hright;
    cbn [reuse_changed] in Hleft, Hright;
    assert (Horiginal : nonempty (Branch sample_a split left_a right_a)) by
      (destruct Hresidenta as [sample_value Hget];
       exists sample_a, sample_value; exact Hget);
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch sample_a split left_a right_a)
      (right := Branch sample_b split left_b right_b);
    [exact Horiginal|
     eapply union_left_specialized_same_branch_correct_wf; eauto].
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
  - solve_changed_case A sample_a sample_b split left_a right_a left_b right_b
      Hwa Hwb Hagree Hleft Hright Eleft Eright Hresidenta.
Qed.

(** Unequal-split reconstruction once routing has established that every key
    of the inner operand belongs to one child of the outer branch. *)
Lemma union_left_specialized_left_outer_left_branch_correct_wf:
  forall (A : Type) sample split (left right operand out_left : t A),
    wf left -> wf right -> wf operand ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) left ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) right ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) operand ->
    (wf out_left /\
      forall key,
        get key out_left =
        match get key left with Some value => Some value | None => get key operand end) ->
    wf (branch sample split out_left right) /\
    forall key,
      get key (branch sample split out_left right) =
      match get key (Branch sample split left right) with
      | Some value => Some value
      | None => get key operand
      end.
Proof.
  intros A sample split left right operand out_left
    Hwl Hwr Hwo Hleft Hright Hoperand [Hwout Hgetout].
  assert (Houtleft : all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) out_left).
  { eapply all_keys_of_combine_lookup with
      (left := left) (right := operand) (out := out_left)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - exact Hwout.
    - intro key. specialize (Hgetout key).
      destruct (get key left); cbn in Hgetout |- *; exact Hgetout.
    - exact Hleft.
    - exact Hoperand. }
  split.
  - now apply branch_wf_general.
  - intro key.
    assert (Houtleftbit : all_keys (fun stored => bit_at stored split = false)
      out_left).
    { eapply all_keys_impl; [exact Houtleft|]. intros stored H. exact (proj2 H). }
    assert (Hrightbit : all_keys (fun stored => bit_at stored split = true) right).
    { eapply all_keys_impl; [exact Hright|]. intros stored H. exact (proj2 H). }
    rewrite (get_branch A sample split out_left right key Houtleftbit Hrightbit).
    destruct (bit_at key split) eqn:E; cbn [get]; rewrite E.
    + assert (Eoperand : get key operand = None).
      { eapply get_none_if_all_keys; [exact Hoperand|].
        intros [_ Hbit]. rewrite E in Hbit. discriminate. }
      rewrite Eoperand. now destruct (get key right).
    + apply Hgetout.
Qed.

(** Changed-result variant of the left-outer, left-child containment case. *)
Lemma union_left_specialized_changed_left_outer_left_branch_correct_wf:
  forall (A : Type) sample split (left right : t A)
      inner_sample inner_split (inner_left inner_right : t A),
    wf (Branch sample split left right) ->
    wf (Branch inner_sample inner_split inner_left inner_right) ->
    split < inner_split ->
    agrees_before_bounded sample inner_sample split = true ->
    bit_at inner_sample split = false ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false)
      (Branch inner_sample inner_split inner_left inner_right) ->
    (wf (union_left_specialized_changed_result left
           (Branch inner_sample inner_split inner_left inner_right)) /\
      forall key,
        get key (union_left_specialized_changed_result left
          (Branch inner_sample inner_split inner_left inner_right)) =
        match get key left with
        | Some value => Some value
        | None => get key (Branch inner_sample inner_split inner_left inner_right)
        end) ->
    wf (union_left_specialized_changed_result
      (Branch sample split left right)
      (Branch inner_sample inner_split inner_left inner_right)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch sample split left right)
        (Branch inner_sample inner_split inner_left inner_right)) =
      match get key (Branch sample split left right) with
      | Some value => Some value
      | None => get key (Branch inner_sample inner_split inner_left inner_right)
      end.
Proof.
  intros A sample split left right inner_sample inner_split inner_left inner_right
    Houter Hinner Hlt Hagree Hside Hoperand Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr Hnl Hnr Hleft Hright Hresident]; subst.
  assert (Eequal : (split =? inner_split) = false) by
    (apply Nat.eqb_neq; lia).
  assert (Eless : (split <? inner_split) = true) by
    (apply Nat.ltb_lt; exact Hlt).
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Eequal, Eless, Hagree, Hside. cbn -[branch reuse_changed].
  destruct (union_left_specialized_changed left
    (Branch inner_sample inner_split inner_left inner_right)) as
    [|changed_key changed_value|changed_sample changed_split changed_left changed_right]
    eqn:Echild.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild |- *.
    destruct (union_left_specialized_left_outer_left_branch_correct_wf A
      sample split left right
      (Branch inner_sample inner_split inner_left inner_right) left
      Hwl Hwr Hinner Hleft Hright Hoperand Hchild) as [_ Hget].
    split; [exact Houter|]. intro key.
    change (get key (Branch sample split left right) =
      match get key (Branch sample split left right) with
      | Some value => Some value
      | None => get key (Branch inner_sample inner_split inner_left inner_right)
      end).
    rewrite <- (get_branch_cached_sample_irrelevant A sample split left right key Hnl Hnr) at 1.
    exact (Hget key).
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch sample split left right)
      (right := Branch inner_sample inner_split inner_left inner_right).
    + destruct Hresident as [sample_value Hget].
      exists sample, sample_value. exact Hget.
    + eapply union_left_specialized_left_outer_left_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch sample split left right)
      (right := Branch inner_sample inner_split inner_left inner_right).
    + destruct Hresident as [sample_value Hget].
      exists sample, sample_value. exact Hget.
    + eapply union_left_specialized_left_outer_left_branch_correct_wf; eauto.
Qed.

Lemma union_left_specialized_left_outer_right_branch_correct_wf:
  forall (A : Type) sample split (left right operand out_right : t A),
    wf left -> wf right -> wf operand ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) left ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) right ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) operand ->
    (wf out_right /\
      forall key,
        get key out_right =
        match get key right with Some value => Some value | None => get key operand end) ->
    wf (branch sample split left out_right) /\
    forall key,
      get key (branch sample split left out_right) =
      match get key (Branch sample split left right) with
      | Some value => Some value
      | None => get key operand
      end.
Proof.
  intros A sample split left right operand out_right
    Hwl Hwr Hwo Hleft Hright Hoperand [Hwout Hgetout].
  assert (Houtright : all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) out_right).
  { eapply all_keys_of_combine_lookup with
      (left := right) (right := operand) (out := out_right)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - exact Hwout.
    - intro key. specialize (Hgetout key).
      destruct (get key right); cbn in Hgetout |- *; exact Hgetout.
    - exact Hright.
    - exact Hoperand. }
  split.
  - now apply branch_wf_general.
  - intro key.
    assert (Hleftbit : all_keys (fun stored => bit_at stored split = false) left).
    { eapply all_keys_impl; [exact Hleft|]. intros stored H. exact (proj2 H). }
    assert (Houtrightbit : all_keys (fun stored => bit_at stored split = true)
      out_right).
    { eapply all_keys_impl; [exact Houtright|]. intros stored H. exact (proj2 H). }
    rewrite (get_branch A sample split left out_right key Hleftbit Houtrightbit).
    destruct (bit_at key split) eqn:E; cbn [get]; rewrite E.
    + apply Hgetout.
    + assert (Eoperand : get key operand = None).
      { eapply get_none_if_all_keys; [exact Hoperand|].
        intros [_ Hbit]. rewrite E in Hbit. discriminate. }
      rewrite Eoperand. now destruct (get key left).
Qed.

(** Changed-result variant of the left-outer, right-child containment case. *)
Lemma union_left_specialized_changed_left_outer_right_branch_correct_wf:
  forall (A : Type) sample split (left right : t A)
      inner_sample inner_split (inner_left inner_right : t A),
    wf (Branch sample split left right) ->
    wf (Branch inner_sample inner_split inner_left inner_right) ->
    split < inner_split ->
    agrees_before_bounded sample inner_sample split = true ->
    bit_at inner_sample split = true ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true)
      (Branch inner_sample inner_split inner_left inner_right) ->
    (wf (union_left_specialized_changed_result right
           (Branch inner_sample inner_split inner_left inner_right)) /\
      forall key,
        get key (union_left_specialized_changed_result right
          (Branch inner_sample inner_split inner_left inner_right)) =
        match get key right with
        | Some value => Some value
        | None => get key (Branch inner_sample inner_split inner_left inner_right)
        end) ->
    wf (union_left_specialized_changed_result
      (Branch sample split left right)
      (Branch inner_sample inner_split inner_left inner_right)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch sample split left right)
        (Branch inner_sample inner_split inner_left inner_right)) =
      match get key (Branch sample split left right) with
      | Some value => Some value
      | None => get key (Branch inner_sample inner_split inner_left inner_right)
      end.
Proof.
  intros A sample split left right inner_sample inner_split inner_left inner_right
    Houter Hinner Hlt Hagree Hside Hoperand Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr Hnl Hnr Hleft Hright Hresident]; subst.
  assert (Eequal : (split =? inner_split) = false) by
    (apply Nat.eqb_neq; lia).
  assert (Eless : (split <? inner_split) = true) by
    (apply Nat.ltb_lt; exact Hlt).
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Eequal, Eless, Hagree, Hside. cbn -[branch reuse_changed].
  destruct (union_left_specialized_changed right
    (Branch inner_sample inner_split inner_left inner_right)) as
    [|changed_key changed_value|changed_sample changed_split changed_left changed_right]
    eqn:Echild.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild |- *.
    destruct (union_left_specialized_left_outer_right_branch_correct_wf A
      sample split left right
      (Branch inner_sample inner_split inner_left inner_right) right
      Hwl Hwr Hinner Hleft Hright Hoperand Hchild) as [_ Hget].
    split; [exact Houter|]. intro key.
    change (get key (Branch sample split left right) =
      match get key (Branch sample split left right) with
      | Some value => Some value
      | None => get key (Branch inner_sample inner_split inner_left inner_right)
      end).
    rewrite <- (get_branch_cached_sample_irrelevant A sample split left right key Hnl Hnr) at 1.
    exact (Hget key).
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch sample split left right)
      (right := Branch inner_sample inner_split inner_left inner_right).
    + destruct Hresident as [sample_value Hget].
      exists sample, sample_value. exact Hget.
    + eapply union_left_specialized_left_outer_right_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch sample split left right)
      (right := Branch inner_sample inner_split inner_left inner_right).
    + destruct Hresident as [sample_value Hget].
      exists sample, sample_value. exact Hget.
    + eapply union_left_specialized_left_outer_right_branch_correct_wf; eauto.
Qed.

(** The worker's successful bounded-prefix test identifies the side occupied
    by every binding of the deeper right branch. *)
Lemma union_left_specialized_left_outer_routing:
  forall (A : Type) outer_sample inner_sample outer_split inner_split
      (inner_left inner_right : t A),
    outer_split < inner_split ->
    agrees_before_bounded outer_sample inner_sample outer_split = true ->
    all_keys (fun key =>
      same_prefix inner_sample key inner_split /\ bit_at key inner_split = false)
      inner_left ->
    all_keys (fun key =>
      same_prefix inner_sample key inner_split /\ bit_at key inner_split = true)
      inner_right ->
    all_keys (fun key =>
      same_prefix outer_sample key outer_split /\
      bit_at key outer_split = bit_at inner_sample outer_split)
      (Branch inner_sample inner_split inner_left inner_right).
Proof.
  intros A outer_sample inner_sample outer_split inner_split inner_left inner_right
    Hlt Hagree Hleft Hright.
  apply all_keys_contained_prefix with
    (inner_sample := inner_sample) (inner_split := inner_split).
  - unfold same_prefix. now apply (proj1
      (agrees_before_bounded_spec outer_sample inner_sample outer_split)).
  - exact Hlt.
  - now apply branch_all_prefix.
Qed.

(** Dual unequal-split reconstruction: the left-biased operand is contained
    in one child of the outer right branch. *)
Lemma union_left_specialized_right_outer_left_branch_correct_wf:
  forall (A : Type) sample split (operand left right out_left : t A),
    wf operand -> wf left -> wf right ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) operand ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) left ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) right ->
    (wf out_left /\
      forall key,
        get key out_left =
        match get key operand with Some value => Some value | None => get key left end) ->
    wf (branch sample split out_left right) /\
    forall key,
      get key (branch sample split out_left right) =
      match get key operand with
      | Some value => Some value
      | None => get key (Branch sample split left right)
      end.
Proof.
  intros A sample split operand left right out_left
    Hwo Hwl Hwr Hoperand Hleft Hright [Hwout Hgetout].
  assert (Houtleft : all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) out_left).
  { eapply all_keys_of_combine_lookup with
      (left := operand) (right := left) (out := out_left)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - exact Hwout.
    - intro key. specialize (Hgetout key).
      destruct (get key operand); cbn in Hgetout |- *; exact Hgetout.
    - exact Hoperand.
    - exact Hleft. }
  split.
  - now apply branch_wf_general.
  - intro key.
    assert (Houtleftbit : all_keys (fun stored => bit_at stored split = false)
      out_left).
    { eapply all_keys_impl; [exact Houtleft|]. intros stored H. exact (proj2 H). }
    assert (Hrightbit : all_keys (fun stored => bit_at stored split = true) right).
    { eapply all_keys_impl; [exact Hright|]. intros stored H. exact (proj2 H). }
    rewrite (get_branch A sample split out_left right key Houtleftbit Hrightbit).
    destruct (bit_at key split) eqn:E; cbn [get]; rewrite E.
    + assert (Eoperand : get key operand = None).
      { eapply get_none_if_all_keys; [exact Hoperand|].
        intros [_ Hbit]. rewrite E in Hbit. discriminate. }
      now rewrite Eoperand.
    + apply Hgetout.
Qed.

Lemma union_left_specialized_right_outer_right_branch_correct_wf:
  forall (A : Type) sample split (operand left right out_right : t A),
    wf operand -> wf left -> wf right ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) operand ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) left ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) right ->
    (wf out_right /\
      forall key,
        get key out_right =
        match get key operand with Some value => Some value | None => get key right end) ->
    wf (branch sample split left out_right) /\
    forall key,
      get key (branch sample split left out_right) =
      match get key operand with
      | Some value => Some value
      | None => get key (Branch sample split left right)
      end.
Proof.
  intros A sample split operand left right out_right
    Hwo Hwl Hwr Hoperand Hleft Hright [Hwout Hgetout].
  assert (Houtright : all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) out_right).
  { eapply all_keys_of_combine_lookup with
      (left := operand) (right := right) (out := out_right)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - exact Hwout.
    - intro key. specialize (Hgetout key).
      destruct (get key operand); cbn in Hgetout |- *; exact Hgetout.
    - exact Hoperand.
    - exact Hright. }
  split.
  - now apply branch_wf_general.
  - intro key.
    assert (Hleftbit : all_keys (fun stored => bit_at stored split = false) left).
    { eapply all_keys_impl; [exact Hleft|]. intros stored H. exact (proj2 H). }
    assert (Houtrightbit : all_keys (fun stored => bit_at stored split = true)
      out_right).
    { eapply all_keys_impl; [exact Houtright|]. intros stored H. exact (proj2 H). }
    rewrite (get_branch A sample split left out_right key Hleftbit Houtrightbit).
    destruct (bit_at key split) eqn:E; cbn [get]; rewrite E.
    + apply Hgetout.
    + assert (Eoperand : get key operand = None).
      { eapply get_none_if_all_keys; [exact Hoperand|].
        intros [_ Hbit]. rewrite E in Hbit. discriminate. }
      now rewrite Eoperand.
Qed.

(** In the right-outer case, even an unchanged routed child must be placed
    under the other outer sibling, so the changed worker always rebuilds. *)
Lemma union_left_specialized_changed_right_outer_left_branch_correct_wf:
  forall (A : Type) inner_sample inner_split (inner_left inner_right : t A)
      outer_sample outer_split (outer_left outer_right : t A),
    wf (Branch inner_sample inner_split inner_left inner_right) ->
    wf (Branch outer_sample outer_split outer_left outer_right) ->
    outer_split < inner_split ->
    agrees_before_bounded inner_sample outer_sample outer_split = true ->
    bit_at inner_sample outer_split = false ->
    all_keys (fun key =>
      same_prefix outer_sample key outer_split /\ bit_at key outer_split = false)
      (Branch inner_sample inner_split inner_left inner_right) ->
    (wf (union_left_specialized_changed_result
           (Branch inner_sample inner_split inner_left inner_right) outer_left) /\
      forall key,
        get key (union_left_specialized_changed_result
          (Branch inner_sample inner_split inner_left inner_right) outer_left) =
        match get key (Branch inner_sample inner_split inner_left inner_right) with
        | Some value => Some value
        | None => get key outer_left
        end) ->
    wf (union_left_specialized_changed_result
      (Branch inner_sample inner_split inner_left inner_right)
      (Branch outer_sample outer_split outer_left outer_right)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch inner_sample inner_split inner_left inner_right)
        (Branch outer_sample outer_split outer_left outer_right)) =
      match get key (Branch inner_sample inner_split inner_left inner_right) with
      | Some value => Some value
      | None => get key (Branch outer_sample outer_split outer_left outer_right)
      end.
Proof.
  intros A inner_sample inner_split inner_left inner_right
    outer_sample outer_split outer_left outer_right
    Hinner Houter Hlt Hagree Hside Hoperand Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr _ _ Hleft Hright _]; subst.
  assert (Eequal : (inner_split =? outer_split) = false) by
    (apply Nat.eqb_neq; lia).
  assert (Enotless : (inner_split <? outer_split) = false) by
    (apply Nat.ltb_ge; lia).
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Eequal, Enotless, Hagree, Hside.
  destruct (union_left_specialized_changed
    (Branch inner_sample inner_split inner_left inner_right) outer_left) as
    [|changed_key changed_value|changed_sample changed_split changed_left changed_right]
    eqn:Echild.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch inner_sample inner_split inner_left inner_right)
      (right := Branch outer_sample outer_split outer_left outer_right).
    + destruct (wf_cached_sample_resident A inner_sample inner_split
        inner_left inner_right Hinner) as [sample_value Hget].
      exists inner_sample, sample_value. exact Hget.
    + eapply union_left_specialized_right_outer_left_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch inner_sample inner_split inner_left inner_right)
      (right := Branch outer_sample outer_split outer_left outer_right).
    + destruct (wf_cached_sample_resident A inner_sample inner_split
        inner_left inner_right Hinner) as [sample_value Hget].
      exists inner_sample, sample_value. exact Hget.
    + eapply union_left_specialized_right_outer_left_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch inner_sample inner_split inner_left inner_right)
      (right := Branch outer_sample outer_split outer_left outer_right).
    + destruct (wf_cached_sample_resident A inner_sample inner_split
        inner_left inner_right Hinner) as [sample_value Hget].
      exists inner_sample, sample_value. exact Hget.
    + eapply union_left_specialized_right_outer_left_branch_correct_wf; eauto.
Qed.

(** Changed-result composition for the right child of an enclosing branch. *)
Lemma union_left_specialized_changed_right_outer_right_branch_correct_wf:
  forall (A : Type) inner_sample inner_split (inner_left inner_right : t A)
      outer_sample outer_split (outer_left outer_right : t A),
    wf (Branch inner_sample inner_split inner_left inner_right) ->
    wf (Branch outer_sample outer_split outer_left outer_right) ->
    outer_split < inner_split ->
    agrees_before_bounded inner_sample outer_sample outer_split = true ->
    bit_at inner_sample outer_split = true ->
    all_keys (fun key =>
      same_prefix outer_sample key outer_split /\ bit_at key outer_split = true)
      (Branch inner_sample inner_split inner_left inner_right) ->
    (wf (union_left_specialized_changed_result
           (Branch inner_sample inner_split inner_left inner_right) outer_right) /\
      forall key,
        get key (union_left_specialized_changed_result
          (Branch inner_sample inner_split inner_left inner_right) outer_right) =
        match get key (Branch inner_sample inner_split inner_left inner_right) with
        | Some value => Some value
        | None => get key outer_right
        end) ->
    wf (union_left_specialized_changed_result
      (Branch inner_sample inner_split inner_left inner_right)
      (Branch outer_sample outer_split outer_left outer_right)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch inner_sample inner_split inner_left inner_right)
        (Branch outer_sample outer_split outer_left outer_right)) =
      match get key (Branch inner_sample inner_split inner_left inner_right) with
      | Some value => Some value
      | None => get key (Branch outer_sample outer_split outer_left outer_right)
      end.
Proof.
  intros A inner_sample inner_split inner_left inner_right
    outer_sample outer_split outer_left outer_right
    Hinner Houter Hlt Hagree Hside Hoperand Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr _ _ Hleft Hright _]; subst.
  assert (Eequal : (inner_split =? outer_split) = false) by
    (apply Nat.eqb_neq; lia).
  assert (Enotless : (inner_split <? outer_split) = false) by
    (apply Nat.ltb_ge; lia).
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Eequal, Enotless, Hagree, Hside.
  destruct (union_left_specialized_changed
    (Branch inner_sample inner_split inner_left inner_right) outer_right) as
    [|changed_key changed_value|changed_sample changed_split changed_left changed_right]
    eqn:Echild.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch inner_sample inner_split inner_left inner_right)
      (right := Branch outer_sample outer_split outer_left outer_right).
    + destruct (wf_cached_sample_resident A inner_sample inner_split
        inner_left inner_right Hinner) as [sample_value Hget].
      exists inner_sample, sample_value. exact Hget.
    + eapply union_left_specialized_right_outer_right_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch inner_sample inner_split inner_left inner_right)
      (right := Branch outer_sample outer_split outer_left outer_right).
    + destruct (wf_cached_sample_resident A inner_sample inner_split
        inner_left inner_right Hinner) as [sample_value Hget].
      exists inner_sample, sample_value. exact Hget.
    + eapply union_left_specialized_right_outer_right_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild. cbn [reuse_changed] in Hchild.
    eapply reuse_changed_correct_nonempty_left with
      (left := Branch inner_sample inner_split inner_left inner_right)
      (right := Branch outer_sample outer_split outer_left outer_right).
    + destruct (wf_cached_sample_resident A inner_sample inner_split
        inner_left inner_right Hinner) as [sample_value Hget].
      exists inner_sample, sample_value. exact Hget.
    + eapply union_left_specialized_right_outer_right_branch_correct_wf; eauto.
Qed.

Lemma union_left_specialized_branch_calls_smaller:
  forall (A : Type) sample_a split_a (left_a right_a : t A)
      sample_b split_b (left_b right_b : t A),
    size left_a + size left_b <
      size (Branch sample_a split_a left_a right_a) +
      size (Branch sample_b split_b left_b right_b) /\
    size right_a + size right_b <
      size (Branch sample_a split_a left_a right_a) +
      size (Branch sample_b split_b left_b right_b) /\
    size left_a + size (Branch sample_b split_b left_b right_b) <
      size (Branch sample_a split_a left_a right_a) +
      size (Branch sample_b split_b left_b right_b) /\
    size right_a + size (Branch sample_b split_b left_b right_b) <
      size (Branch sample_a split_a left_a right_a) +
      size (Branch sample_b split_b left_b right_b) /\
    size (Branch sample_a split_a left_a right_a) + size left_b <
      size (Branch sample_a split_a left_a right_a) +
      size (Branch sample_b split_b left_b right_b) /\
    size (Branch sample_a split_a left_a right_a) + size right_b <
      size (Branch sample_a split_a left_a right_a) +
      size (Branch sample_b split_b left_b right_b).
Proof. intros. cbn [size]. lia. Qed.

(** A failed bounded-prefix comparison is the terminal join case of the
    worker.  Repackage the existing separated-join proof in that exact form. *)
Lemma union_left_specialized_disjoint_branches_correct_wf:
  forall (A : Type) sample_a split_a (left_a right_a : t A)
      sample_b split_b (left_b right_b : t A),
    wf (Branch sample_a split_a left_a right_a) ->
    wf (Branch sample_b split_b left_b right_b) ->
    agrees_before_bounded sample_a sample_b (Nat.min split_a split_b) = false ->
    wf (join (Branch sample_a split_a left_a right_a)
             (Branch sample_b split_b left_b right_b)) /\
    forall key,
      get key (join (Branch sample_a split_a left_a right_a)
                    (Branch sample_b split_b left_b right_b)) =
      match get key (Branch sample_a split_a left_a right_a) with
      | Some value => Some value
      | None => get key (Branch sample_b split_b left_b right_b)
      end.
Proof.
  intros A sample_a split_a left_a right_a sample_b split_b left_b right_b
    Hwa Hwb Hdisagree.
  inversion Hwa as [| |? ? ? ? _ _ _ _ Hla Hra _]; subst.
  inversion Hwb as [| |? ? ? ? _ _ _ _ Hlb Hrb _]; subst.
  destruct (branches_disjoint_prefix A A sample_a split_a
    (Branch sample_a split_a left_a right_a) sample_b split_b
    (Branch sample_b split_b left_b right_b)) as [differing
      [Hdiff [Hleft Hright]]].
  - now apply branch_all_prefix.
  - now apply branch_all_prefix.
  - exact Hdisagree.
  - eapply join_separated_correct_wf; eauto.
Qed.

(** The specialized worker has the same invariant and left-biased lookup
    contract as the established union.  The induction measure is the combined
    number of constructors; the six possible recursive calls are covered by
    [union_left_specialized_branch_calls_smaller]. *)
Theorem union_left_specialized_correct_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    wf (union_left_specialized left right) /\
    forall key,
      get key (union_left_specialized left right) =
      match get key left with
      | Some value => Some value
      | None => get key right
      end.
Proof.
  intros A.
  assert (Hstrong : forall total, forall (left right : t A),
      size left + size right = total -> wf left -> wf right ->
      wf (union_left_specialized left right) /\
      forall key,
        get key (union_left_specialized left right) =
        match get key left with
        | Some value => Some value
        | None => get key right
        end).
  { intro total. induction total using lt_wf_ind.
    intros left right E Hwl Hwr.
    destruct left as [|left_key left_value
        |left_sample left_split left_left left_right];
      destruct right as [|right_key right_value
        |right_sample right_split right_left right_right].
    - split; [constructor|]. intro key. reflexivity.
    - split; [exact Hwr|]. intro key. reflexivity.
    - split; [exact Hwr|]. intro key. reflexivity.
    - split; [exact Hwl|]. intro key.
      rewrite union_left_specialized_equation. cbn.
      destruct (String.eqb key left_key); reflexivity.
    - now apply union_left_specialized_leaf_left_correct_wf.
    - now apply union_left_specialized_leaf_left_correct_wf.
    - split; [exact Hwl|]. intro key.
      rewrite union_left_specialized_equation. cbn.
      destruct (bit_at key left_split) eqn:Ebit; cbn [get];
        [destruct (get key left_right)|destruct (get key left_left)]; reflexivity.
    - now apply union_left_specialized_leaf_right_correct_wf.
    - inversion Hwl as
        [| |? ? ? ? Hwll Hwlr _ _ Hall Halr _]; subst.
      inversion Hwr as
        [| |? ? ? ? Hwrl Hwrr _ _ Harl Harr _]; subst.
      rewrite union_left_specialized_equation.
      destruct (left_split =? right_split) eqn:Esplits.
      + apply Nat.eqb_eq in Esplits. subst right_split.
        destruct (agrees_before_bounded left_sample right_sample left_split)
          eqn:Eagrees.
        * destruct (H (size left_left + size right_left)
            ltac:(cbn [size]; lia) left_left right_left eq_refl Hwll Hwrl)
            as [Hwoutl Hgetoutl].
          destruct (H (size left_right + size right_right)
            ltac:(cbn [size]; lia) left_right right_right eq_refl Hwlr Hwrr)
            as [Hwoutr Hgetoutr].
          eapply union_left_specialized_same_branch_correct_wf; eauto.
        * destruct (union_left_specialized_disjoint_branches_correct_wf A
            left_sample left_split left_left left_right right_sample
            left_split right_left right_right Hwl Hwr
            ltac:(now rewrite Nat.min_id))
            as [Hwj Hgetj].
          exact (conj Hwj Hgetj).
      + destruct (left_split <? right_split) eqn:Eorder.
        * apply Nat.ltb_lt in Eorder.
          destruct (agrees_before_bounded left_sample right_sample left_split)
            eqn:Eagrees.
          -- assert (Hoperand : all_keys (fun key =>
                 same_prefix left_sample key left_split /\
                 bit_at key left_split = bit_at right_sample left_split)
                 (Branch right_sample right_split right_left right_right)).
             { eapply union_left_specialized_left_outer_routing; eauto. }
             destruct (bit_at right_sample left_split) eqn:Eside.
             ++ destruct (H (size left_right +
                   size (Branch right_sample right_split right_left right_right))
                 ltac:(cbn [size]; lia) left_right
                 (Branch right_sample right_split right_left right_right)
                 eq_refl Hwlr Hwr) as [Hwout Hgetout].
                eapply union_left_specialized_left_outer_right_branch_correct_wf
                  with (operand := Branch right_sample right_split right_left right_right);
                  eauto.
             ++ destruct (H (size left_left +
                   size (Branch right_sample right_split right_left right_right))
                 ltac:(cbn [size]; lia) left_left
                 (Branch right_sample right_split right_left right_right)
                 eq_refl Hwll Hwr) as [Hwout Hgetout].
                eapply union_left_specialized_left_outer_left_branch_correct_wf
                  with (operand := Branch right_sample right_split right_left right_right);
                  eauto.
          -- destruct (union_left_specialized_disjoint_branches_correct_wf A
               left_sample left_split left_left left_right right_sample
               right_split right_left right_right Hwl Hwr
               ltac:(rewrite Nat.min_l by lia; exact Eagrees))
               as [Hwj Hgetj].
             exact (conj Hwj Hgetj).
        * apply Nat.ltb_ge in Eorder.
          assert (Hreverse : right_split < left_split) by
            (apply Nat.eqb_neq in Esplits; lia).
          destruct (agrees_before_bounded left_sample right_sample right_split)
            eqn:Eagrees.
          -- assert (Hoperand : all_keys (fun key =>
                 same_prefix right_sample key right_split /\
                 bit_at key right_split = bit_at left_sample right_split)
                 (Branch left_sample left_split left_left left_right)).
             { eapply all_keys_contained_prefix with
                 (inner_sample := left_sample) (inner_split := left_split).
               - unfold same_prefix. intros n Hn.
                 symmetry.
                 apply (proj1 (agrees_before_bounded_spec
                   left_sample right_sample right_split) Eagrees).
                 exact Hn.
               - exact Hreverse.
               - now apply branch_all_prefix. }
             destruct (bit_at left_sample right_split) eqn:Eside.
             ++ destruct (H (size (Branch left_sample left_split left_left left_right) +
                   size right_right) ltac:(cbn [size]; lia)
                 (Branch left_sample left_split left_left left_right) right_right
                 eq_refl Hwl Hwrr) as [Hwout Hgetout].
                eapply union_left_specialized_right_outer_right_branch_correct_wf
                  with (operand := Branch left_sample left_split left_left left_right);
                  eauto.
             ++ destruct (H (size (Branch left_sample left_split left_left left_right) +
                   size right_left) ltac:(cbn [size]; lia)
                 (Branch left_sample left_split left_left left_right) right_left
                 eq_refl Hwl Hwrl) as [Hwout Hgetout].
                eapply union_left_specialized_right_outer_left_branch_correct_wf
                  with (operand := Branch left_sample left_split left_left left_right);
                  eauto.
          -- destruct (union_left_specialized_disjoint_branches_correct_wf A
               left_sample left_split left_left left_right right_sample
               right_split right_left right_right Hwl Hwr
               ltac:(rewrite Nat.min_r by lia; exact Eagrees))
               as [Hwj Hgetj].
             exact (conj Hwj Hgetj).
  }
  intros left right Hwl Hwr.
  eapply Hstrong with (total := size left + size right); eauto.
Qed.

(** The source-visible signal refines the specialized worker: interpreting
    [None] as the original first input has the usual left-biased union law. *)
Theorem union_left_specialized_changed_correct_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    wf (union_left_specialized_changed_result left right) /\
    forall key,
      get key (union_left_specialized_changed_result left right) =
      match get key left with
      | Some value => Some value
      | None => get key right
      end.
Proof.
  intros A.
  assert (Hstrong : forall total, forall (left right : t A),
      size left + size right = total -> wf left -> wf right ->
      wf (union_left_specialized_changed_result left right) /\
      forall key,
        get key (union_left_specialized_changed_result left right) =
        match get key left with
        | Some value => Some value
        | None => get key right
        end).
  { intro total. induction total using lt_wf_ind.
    intros left right E Hwl Hwr.
    destruct left as [|left_key left_value
        |left_sample left_split left_left left_right];
      destruct right as [|right_key right_value
        |right_sample right_split right_left right_right].
    - rewrite union_left_specialized_changed_empty_left.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_empty_left.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_empty_left.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_leaf_left by exact Hwr.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_leaf_left by exact Hwr.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_leaf_left by exact Hwr.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_empty_right.
      now apply union_left_specialized_correct_wf.
    - rewrite union_left_specialized_changed_leaf_right by exact Hwl.
      now apply union_left_specialized_correct_wf.
    - inversion Hwl as
        [| |? ? ? ? Hwll Hwlr _ _ Hall Halr _]; subst.
      inversion Hwr as
        [| |? ? ? ? Hwrl Hwrr _ _ Harl Harr _]; subst.
      destruct (left_split =? right_split) eqn:Esplits.
      + apply Nat.eqb_eq in Esplits. subst right_split.
        destruct (agrees_before_bounded left_sample right_sample left_split)
          eqn:Eagrees.
        * destruct (H (size left_left + size right_left)
            ltac:(cbn [size]; lia) left_left right_left eq_refl Hwll Hwrl)
            as [Hwoutl Hgetoutl].
          destruct (H (size left_right + size right_right)
            ltac:(cbn [size]; lia) left_right right_right eq_refl Hwlr Hwrr)
            as [Hwoutr Hgetoutr].
          eapply union_left_specialized_changed_same_branch_correct_wf; eauto.
        * destruct (union_left_specialized_disjoint_branches_correct_wf A
            left_sample left_split left_left left_right right_sample
            left_split right_left right_right Hwl Hwr
            ltac:(now rewrite Nat.min_id)) as [Hwj Hgetj].
          unfold union_left_specialized_changed_result.
          rewrite union_left_specialized_changed_equation.
          rewrite Nat.eqb_refl, Eagrees.
          eapply reuse_changed_correct_nonempty_left with
            (left := Branch left_sample left_split left_left left_right)
            (right := Branch right_sample left_split right_left right_right);
            [destruct (wf_cached_sample_resident A left_sample left_split
              left_left left_right Hwl) as [sample_value Hget];
             exists left_sample, sample_value; exact Hget
            |exact (conj Hwj Hgetj)].
      + destruct (left_split <? right_split) eqn:Eorder.
        * apply Nat.ltb_lt in Eorder.
          destruct (agrees_before_bounded left_sample right_sample left_split)
            eqn:Eagrees.
          -- assert (Hoperand : all_keys (fun key =>
                 same_prefix left_sample key left_split /\
                 bit_at key left_split = bit_at right_sample left_split)
                 (Branch right_sample right_split right_left right_right)).
             { eapply union_left_specialized_left_outer_routing; eauto. }
             destruct (bit_at right_sample left_split) eqn:Eside.
             ++ destruct (H (size left_right +
                   size (Branch right_sample right_split right_left right_right))
                 ltac:(cbn [size]; lia) left_right
                 (Branch right_sample right_split right_left right_right)
                 eq_refl Hwlr Hwr) as [Hwout Hgetout].
                eapply union_left_specialized_changed_left_outer_right_branch_correct_wf;
                  eauto.
             ++ destruct (H (size left_left +
                   size (Branch right_sample right_split right_left right_right))
                 ltac:(cbn [size]; lia) left_left
                 (Branch right_sample right_split right_left right_right)
                 eq_refl Hwll Hwr) as [Hwout Hgetout].
                eapply union_left_specialized_changed_left_outer_left_branch_correct_wf;
                  eauto.
          -- destruct (union_left_specialized_disjoint_branches_correct_wf A
               left_sample left_split left_left left_right right_sample
               right_split right_left right_right Hwl Hwr
               ltac:(rewrite Nat.min_l by lia; exact Eagrees)) as [Hwj Hgetj].
             unfold union_left_specialized_changed_result.
             rewrite union_left_specialized_changed_equation.
             assert (Eorderb : (left_split <? right_split) = true) by
               (apply Nat.ltb_lt; exact Eorder).
             rewrite Esplits, Eorderb, Eagrees.
             eapply reuse_changed_correct_nonempty_left with
               (left := Branch left_sample left_split left_left left_right)
               (right := Branch right_sample right_split right_left right_right);
               [destruct (wf_cached_sample_resident A left_sample left_split
                 left_left left_right Hwl) as [sample_value Hget];
                exists left_sample, sample_value; exact Hget
               |exact (conj Hwj Hgetj)].
        * apply Nat.ltb_ge in Eorder.
          assert (Hreverse : right_split < left_split) by
            (apply Nat.eqb_neq in Esplits; lia).
          destruct (agrees_before_bounded left_sample right_sample right_split)
            eqn:Eagrees.
          -- assert (Hoperand : all_keys (fun key =>
                 same_prefix right_sample key right_split /\
                 bit_at key right_split = bit_at left_sample right_split)
                 (Branch left_sample left_split left_left left_right)).
             { eapply all_keys_contained_prefix with
                 (inner_sample := left_sample) (inner_split := left_split).
               - unfold same_prefix. intros n Hn. symmetry.
                 apply (proj1 (agrees_before_bounded_spec
                   left_sample right_sample right_split) Eagrees).
                 exact Hn.
               - exact Hreverse.
               - now apply branch_all_prefix. }
             destruct (bit_at left_sample right_split) eqn:Eside.
             ++ destruct (H (size (Branch left_sample left_split left_left left_right) +
                   size right_right) ltac:(cbn [size]; lia)
                 (Branch left_sample left_split left_left left_right) right_right
                 eq_refl Hwl Hwrr) as [Hwout Hgetout].
                eapply union_left_specialized_changed_right_outer_right_branch_correct_wf;
                  eauto.
             ++ destruct (H (size (Branch left_sample left_split left_left left_right) +
                   size right_left) ltac:(cbn [size]; lia)
                 (Branch left_sample left_split left_left left_right) right_left
                 eq_refl Hwl Hwrl) as [Hwout Hgetout].
                eapply union_left_specialized_changed_right_outer_left_branch_correct_wf;
                  eauto.
          -- destruct (union_left_specialized_disjoint_branches_correct_wf A
               left_sample left_split left_left left_right right_sample
               right_split right_left right_right Hwl Hwr
               ltac:(rewrite Nat.min_r by lia; exact Eagrees)) as [Hwj Hgetj].
             unfold union_left_specialized_changed_result.
             rewrite union_left_specialized_changed_equation.
             assert (Eorderb : (left_split <? right_split) = false) by
               (apply Nat.ltb_ge; exact Eorder).
             rewrite Esplits, Eorderb, Eagrees.
             eapply reuse_changed_correct_nonempty_left with
               (left := Branch left_sample left_split left_left left_right)
               (right := Branch right_sample right_split right_left right_right);
               [destruct (wf_cached_sample_resident A left_sample left_split
                 left_left left_right Hwl) as [sample_value Hget];
                exists left_sample, sample_value; exact Hget
               |exact (conj Hwj Hgetj)].
  }
  intros left right Hwl Hwr.
  eapply Hstrong with (total := size left + size right); eauto.
Qed.

Theorem union_right_specialized_changed_correct_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    wf (union_right_specialized_changed_result left right) /\
    forall key,
      get key (union_right_specialized_changed_result left right) =
      match get key right with
      | Some value => Some value
      | None => get key left
      end.
Proof.
  intros A left right Hleft Hright.
  unfold union_right_specialized_changed_result.
  now apply union_left_specialized_changed_correct_wf.
Qed.

Theorem union_right_specialized_correct_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    wf (union_right_specialized left right) /\
    forall key,
      get key (union_right_specialized left right) =
      match get key right with
      | Some value => Some value
      | None => get key left
      end.
Proof.
  intros A left right Hleft Hright.
  unfold union_right_specialized.
  now apply union_left_specialized_correct_wf.
Qed.

(** The direct fuel worker is an extraction-shape variant of the proved
    changed worker.  Its counter is strictly larger than the combined source
    tree size, so every recursive pair has a remaining sufficient counter. *)
Theorem union_left_specialized_changed_fuel_exact:
  forall (A : Type) (fuel : nat) (left right : t A),
    size left + size right < fuel ->
    union_left_specialized_changed_fuel fuel left right =
    union_left_specialized_changed left right.
Proof.
  intros A.
  assert (Hstrong : forall total, forall fuel (left right : t A),
      size left + size right = total -> total < fuel ->
      union_left_specialized_changed_fuel fuel left right =
      union_left_specialized_changed left right).
  { intro total. induction total using lt_wf_ind.
    intros fuel left right Esize Hfuel.
    destruct fuel as [|fuel']; [lia|].
    destruct left as [|left_key left_value
        |left_sample left_split left_left left_right];
      destruct right as [|right_key right_value
        |right_sample right_split right_left right_right];
      try reflexivity.
    cbn [size] in Esize.
    assert (Ell : union_left_specialized_changed_fuel fuel' left_left right_left =
        union_left_specialized_changed left_left right_left).
    { eapply H with (m := size left_left + size right_left);
        [cbn [size]; lia|reflexivity|lia]. }
    assert (Err : union_left_specialized_changed_fuel fuel' left_right right_right =
        union_left_specialized_changed left_right right_right).
    { eapply H with (m := size left_right + size right_right);
        [cbn [size]; lia|reflexivity|lia]. }
    assert (Elb : union_left_specialized_changed_fuel fuel' left_left
        (Branch right_sample right_split right_left right_right) =
        union_left_specialized_changed left_left
          (Branch right_sample right_split right_left right_right)).
    { assert (Hsmaller : size left_left +
          size (Branch right_sample right_split right_left right_right) < total).
      { cbn [size] in Esize |- *. lia. }
      assert (Hfuel' : size left_left +
          size (Branch right_sample right_split right_left right_right) < fuel') by lia.
      eapply H with (m := size left_left +
        size (Branch right_sample right_split right_left right_right)); eauto. }
    assert (Erb : union_left_specialized_changed_fuel fuel' left_right
        (Branch right_sample right_split right_left right_right) =
        union_left_specialized_changed left_right
          (Branch right_sample right_split right_left right_right)).
    { assert (Hsmaller : size left_right +
          size (Branch right_sample right_split right_left right_right) < total).
      { cbn [size] in Esize |- *. lia. }
      assert (Hfuel' : size left_right +
          size (Branch right_sample right_split right_left right_right) < fuel') by lia.
      eapply H with (m := size left_right +
        size (Branch right_sample right_split right_left right_right)); eauto. }
    assert (Eal : union_left_specialized_changed_fuel fuel'
        (Branch left_sample left_split left_left left_right) right_left =
        union_left_specialized_changed
          (Branch left_sample left_split left_left left_right) right_left).
    { assert (Hsmaller : size (Branch left_sample left_split left_left left_right) +
          size right_left < total).
      { cbn [size] in Esize |- *. lia. }
      assert (Hfuel' : size (Branch left_sample left_split left_left left_right) +
          size right_left < fuel') by lia.
      eapply H with (m := size (Branch left_sample left_split left_left left_right) +
        size right_left); eauto. }
    assert (Ear : union_left_specialized_changed_fuel fuel'
        (Branch left_sample left_split left_left left_right) right_right =
        union_left_specialized_changed
          (Branch left_sample left_split left_left left_right) right_right).
    { assert (Hsmaller : size (Branch left_sample left_split left_left left_right) +
          size right_right < total).
      { cbn [size] in Esize |- *. lia. }
      assert (Hfuel' : size (Branch left_sample left_split left_left left_right) +
          size right_right < fuel') by lia.
      eapply H with (m := size (Branch left_sample left_split left_left left_right) +
        size right_right); eauto. }
    cbn [union_left_specialized_changed_fuel].
    rewrite union_left_specialized_changed_equation.
    rewrite Ell, Err, Elb, Erb, Eal, Ear.
    reflexivity.
  }
  intros fuel left right Hfuel.
  eapply Hstrong with (total := size left + size right); eauto.
Qed.

Theorem union_left_specialized_changed_fuel_result_exact:
  forall (A : Type) (left right : t A),
    union_left_specialized_changed_fuel_result left right =
    union_left_specialized_changed_result left right.
Proof.
  intros A left right.
  unfold union_left_specialized_changed_fuel_result,
    union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_fuel_exact by lia.
  reflexivity.
Qed.
