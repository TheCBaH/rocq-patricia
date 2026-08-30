(** Focused certificates and refinement proof workspace for
    [PatriciaUnion].  Recompiling this file reuses the cached core proof. *)

From Stdlib Require Import Arith.Wf_nat Bool Lia NArith.
Require Import PatriciaBits Patricia PatriciaProof PatriciaUnion.

Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros A left. destruct left; reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. reflexivity. Qed.

(** The changed worker agrees definitionally with the original worker in all
    non-recursive shapes.  These bridge lemmas keep the eventual changed
    worker proof focused solely on branch/branch reconstruction. *)
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
    union_left_specialized_changed_result (Leaf key value) right =
    union_left_specialized (Leaf key value) right.
Proof.
  intros A key value right. destruct right;
    unfold union_left_specialized_changed_result,
      union_left_specialized_changed, union_left_specialized; cbn;
    try reflexivity.
  destruct (Pos.eqb key key0); reflexivity.
Qed.

Lemma union_left_specialized_changed_leaf_right:
  forall (A : Type) (left : t A) key (value : A),
    union_left_specialized_changed_result left (Leaf key value) =
    union_left_specialized left (Leaf key value).
Proof.
  intros A left key value. destruct left as [|stored stored_value|p m l r].
  - reflexivity.
  - unfold union_left_specialized_changed_result,
      union_left_specialized_changed, union_left_specialized; cbn.
    destruct (Pos.eqb stored key); reflexivity.
  - unfold union_left_specialized_changed_result,
      union_left_specialized_changed, union_left_specialized; cbn.
    destruct (matches_prefix key p m) eqn:P; cbn [get].
    + destruct (zero_bit key m) eqn:Z;
        [destruct (get key l)|destruct (get key r)]; reflexivity.
    + reflexivity.
Qed.

Theorem union_left_specialized_disjoint_masks:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    (N.eqb ma mb && N.eqb pa pb)%bool = false ->
    mask_above ma mb = false ->
    mask_above mb ma = false ->
    union_left_specialized (Branch pa ma la ra) (Branch pb mb lb rb) =
    join (Branch pa ma la ra) (Branch pb mb lb rb).
Proof.
  intros A pa ma la ra pb mb lb rb Hsame Hab Hba.
  cbn [union_left_specialized]. rewrite Hsame, Hab, Hba. reflexivity.
Qed.

(** The non-recursive leaf cases already have the full biased-union
    contract.  Keeping them separate makes the remaining branch/branch proof
    depend only on the recursive routing cases. *)
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
  destruct right as [|right_key right_value|prefix mask left right].
  - split; [constructor|]. intro query. cbn [union_left_specialized get].
    destruct (Pos.eqb query key); reflexivity.
  - rewrite union_left_specialized_equation.
    destruct (Pos.eqb key right_key) eqn:E.
    + apply Pos.eqb_eq in E. subst right_key.
      split; [constructor|]. intro query. cbn [get].
      destruct (Pos.eqb query key); reflexivity.
    + destruct (set_correct_wf key value Hright) as [Hwf Hget].
      split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
      destruct (Pos.eqb query key); reflexivity.
  - destruct (set_correct_wf key value Hright) as [Hwf Hget].
    split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
    destruct (Pos.eqb query key); reflexivity.
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
  destruct left as [|left_key left_value|prefix mask left right].
  - split; [constructor|]. intro query. cbn [union_left_specialized]. reflexivity.
  - rewrite union_left_specialized_equation.
    destruct (Pos.eqb left_key key) eqn:E.
    + apply Pos.eqb_eq in E. subst left_key.
      split; [constructor|]. intro query. cbn [get].
      destruct (Pos.eqb query key); reflexivity.
    + destruct (@set_correct_wf A left_key left_value (Leaf key value)
        (@wf_leaf A key value)) as [Hwf Hget].
      split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
      destruct (Pos.eqb query left_key); reflexivity.
  - rewrite union_left_specialized_equation.
    destruct (get key (Branch prefix mask left right)) as [found|] eqn:E.
    + split; [exact Hleft|]. intro query.
      change (get query (Branch prefix mask left right) =
        match get query (Branch prefix mask left right) with
        | Some current => Some current
        | None => get query (Leaf key value)
        end).
      destruct (get query (Branch prefix mask left right)) as [current|] eqn:Q;
        [reflexivity|].
      destruct (Pos.eqb query key) eqn:K.
      * apply Pos.eqb_eq in K. subst query. rewrite E in Q. discriminate.
      * cbn [get]. now rewrite K.
    + destruct (set_correct_wf key value Hleft) as [Hwf Hget].
      split; [exact Hwf|]. intro query. rewrite Hget. cbn [get].
      destruct (Pos.eqb query key) eqn:K.
      * apply Pos.eqb_eq in K. subst query.
        change (Some value =
          match get key (Branch prefix mask left right) with
          | Some current => Some current
          | None => Some value
          end).
        now rewrite E.
      * change (get query (Branch prefix mask left right) =
          match get query (Branch prefix mask left right) with
          | Some current => Some current
          | None => None
          end).
        destruct (get query (Branch prefix mask left right)); reflexivity.
Qed.

(** Rebuild the common-split case from the contracts of its two recursive
    calls.  This is the first branch/branch routing case and is shared by the
    eventual well-founded proof of the whole worker. *)
Lemma union_left_specialized_same_branch_correct_wf:
  forall (A : Type) prefix mask (left_a right_a left_b right_b : t A)
      (out_left out_right : t A),
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      left_a ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      right_a ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      left_b ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      right_b ->
    (wf out_left /\
      forall key,
        get key out_left =
        match get key left_a with Some value => Some value | None => get key left_b end) ->
    (wf out_right /\
      forall key,
        get key out_right =
        match get key right_a with Some value => Some value | None => get key right_b end) ->
    wf (branch prefix mask out_left out_right) /\
    forall key,
      get key (branch prefix mask out_left out_right) =
      match get key (Branch prefix mask left_a right_a) with
      | Some value => Some value
      | None => get key (Branch prefix mask left_b right_b)
      end.
Proof.
  intros A prefix mask left_a right_a left_b right_b out_left out_right
    Hla Hra Hlb Hrb [Hwol Hgetol] [Hwor Hgetor].
  assert (Hall : all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      out_left).
  { eapply all_keys_of_combine_lookup with
      (left := left_a) (right := left_b) (out := out_left)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - intro key. specialize (Hgetol key).
      destruct (get key left_a); cbn in Hgetol |- *; exact Hgetol.
    - exact Hla.
    - exact Hlb. }
  assert (Har : all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      out_right).
  { eapply all_keys_of_combine_lookup with
      (left := right_a) (right := right_b) (out := out_right)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - intro key. specialize (Hgetor key).
      destruct (get key right_a); cbn in Hgetor |- *; exact Hgetor.
    - exact Hra.
    - exact Hrb. }
  split.
  - now apply branch_wf.
  - intro key. rewrite get_branch by assumption. cbn [get].
    destruct (matches_prefix key prefix mask) eqn:Kprefix;
      [destruct (zero_bit key mask) eqn:Kbit|]; cbn;
      rewrite ?Kprefix, ?Kbit; auto.
Qed.

(** Changed-result composition for equal integer branch headers. *)
Lemma union_left_specialized_changed_same_branch_correct_wf:
  forall (A : Type) prefix mask (left_a right_a left_b right_b : t A),
    wf (Branch prefix mask left_a right_a) ->
    wf (Branch prefix mask left_b right_b) ->
    (wf (union_left_specialized_changed_result left_a left_b) /\
      forall key,
        get key (union_left_specialized_changed_result left_a left_b) =
        match get key left_a with Some value => Some value | None => get key left_b end) ->
    (wf (union_left_specialized_changed_result right_a right_b) /\
      forall key,
        get key (union_left_specialized_changed_result right_a right_b) =
        match get key right_a with Some value => Some value | None => get key right_b end) ->
    wf (union_left_specialized_changed_result
      (Branch prefix mask left_a right_a) (Branch prefix mask left_b right_b)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch prefix mask left_a right_a) (Branch prefix mask left_b right_b)) =
      match get key (Branch prefix mask left_a right_a) with
      | Some value => Some value
      | None => get key (Branch prefix mask left_b right_b)
      end.
Proof.
  intros A prefix mask left_a right_a left_b right_b Hwa Hwb Hleft Hright.
  inversion Hwa as [| |? ? ? ? Hwla Hwra Hnla Hnra Hla Hra]; subst.
  inversion Hwb as [| |? ? ? ? Hwlb Hwrb Hnlb Hnrb Hlb Hrb]; subst.
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite !N.eqb_refl. cbn.
  destruct (union_left_specialized_changed left_a left_b) eqn:Eleft;
    destruct (union_left_specialized_changed right_a right_b) eqn:Eright.
  - unfold union_left_specialized_changed_result in Hleft, Hright.
    rewrite Eleft in Hleft. rewrite Eright in Hright.
    eapply union_left_specialized_same_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hleft, Hright.
    rewrite Eleft in Hleft. rewrite Eright in Hright.
    eapply union_left_specialized_same_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hleft, Hright.
    rewrite Eleft in Hleft. rewrite Eright in Hright.
    eapply union_left_specialized_same_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hleft, Hright.
    rewrite Eleft in Hleft. rewrite Eright in Hright.
    assert (Ebranch : branch prefix mask left_a right_a =
      Branch prefix mask left_a right_a).
    { now apply branch_unchanged. }
    rewrite <- Ebranch.
    eapply union_left_specialized_same_branch_correct_wf; eauto.
Qed.

(** When every binding of the right operand lies in the left side of the
    outer branch, only that child needs a recursive union. *)
Lemma union_left_specialized_left_outer_branch_correct_wf:
  forall (A : Type) prefix mask (left right operand out_left : t A),
    wf left -> wf right -> wf operand ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      left ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      right ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      operand ->
    (wf out_left /\
      forall key,
        get key out_left =
        match get key left with Some value => Some value | None => get key operand end) ->
    wf (branch prefix mask out_left right) /\
    forall key,
      get key (branch prefix mask out_left right) =
      match get key (Branch prefix mask left right) with
      | Some value => Some value
      | None => get key operand
      end.
Proof.
  intros A prefix mask left right operand out_left
    Hwl Hwr Hwo Hleft Hright Hoperand [Hwout Hgetout].
  assert (Houtleft : all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      out_left).
  { eapply all_keys_of_combine_lookup with
      (left := left) (right := operand) (out := out_left)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - intro key. specialize (Hgetout key).
      destruct (get key left); cbn in Hgetout |- *; exact Hgetout.
    - exact Hleft.
    - exact Hoperand. }
  split.
  - now apply branch_wf.
  - intro key. rewrite get_branch by assumption. cbn [get].
    destruct (matches_prefix key prefix mask) eqn:P.
    + destruct (zero_bit key mask) eqn:Z.
      * apply Hgetout.
      * assert (Eoperand : get key operand = None).
        { eapply all_keys_none; [exact Hoperand|].
          intros [_ Hbit]. rewrite Z in Hbit. discriminate. }
        rewrite Eoperand. now destruct (get key right).
    + assert (Eoperand : get key operand = None).
      { eapply all_keys_none; [exact Hoperand|].
        intros [Hprefix _]. rewrite P in Hprefix. discriminate. }
      now rewrite Eoperand.
Qed.

(** Changed-result composition for a left-outer zero-bit route. *)
Lemma union_left_specialized_changed_left_outer_left_branch_correct_wf:
  forall (A : Type) prefix mask (left right : t A)
      operand_prefix operand_mask (operand_left operand_right : t A) key,
    wf (Branch prefix mask left right) ->
    wf (Branch operand_prefix operand_mask operand_left operand_right) ->
    (N.eqb mask operand_mask && N.eqb prefix operand_prefix)%bool = false ->
    mask_above mask operand_mask = true ->
    representative (Branch operand_prefix operand_mask operand_left operand_right) = Some key ->
    matches_prefix key prefix mask = true ->
    zero_bit key mask = true ->
    all_keys (fun stored =>
      matches_prefix stored prefix mask = true /\ zero_bit stored mask = true)
      (Branch operand_prefix operand_mask operand_left operand_right) ->
    (wf (union_left_specialized_changed_result left
           (Branch operand_prefix operand_mask operand_left operand_right)) /\
      forall stored,
        get stored (union_left_specialized_changed_result left
          (Branch operand_prefix operand_mask operand_left operand_right)) =
        match get stored left with
        | Some value => Some value
        | None => get stored (Branch operand_prefix operand_mask operand_left operand_right)
        end) ->
    wf (union_left_specialized_changed_result
      (Branch prefix mask left right)
      (Branch operand_prefix operand_mask operand_left operand_right)) /\
    forall stored,
      get stored (union_left_specialized_changed_result
        (Branch prefix mask left right)
        (Branch operand_prefix operand_mask operand_left operand_right)) =
      match get stored (Branch prefix mask left right) with
      | Some value => Some value
      | None => get stored (Branch operand_prefix operand_mask operand_left operand_right)
      end.
Proof.
  intros A prefix mask left right operand_prefix operand_mask operand_left operand_right key
    Houter Hoperand Hsame Habove Hrep Hprefix Hside Hall Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr Hnl Hnr Hleft Hright]; subst.
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Habove, Hrep, Hprefix, Hside.
  destruct (union_left_specialized_changed left
    (Branch operand_prefix operand_mask operand_left operand_right)) eqn:Echild.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild.
    eapply union_left_specialized_left_outer_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild.
    destruct (union_left_specialized_left_outer_branch_correct_wf A prefix mask
      left right (Branch operand_prefix operand_mask operand_left operand_right) left
      Hwl Hwr Hoperand Hleft Hright Hall Hchild) as [_ Hget].
    split; [exact Houter|]. intro stored.
    assert (Ebranch : branch prefix mask left right = Branch prefix mask left right).
    { now apply branch_unchanged. }
    rewrite <- Ebranch at 1.
    apply Hget.
Qed.

Lemma union_left_specialized_left_outer_right_branch_correct_wf:
  forall (A : Type) prefix mask (left right operand out_right : t A),
    wf left -> wf right -> wf operand ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      left ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      right ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      operand ->
    (wf out_right /\
      forall key,
        get key out_right =
        match get key right with Some value => Some value | None => get key operand end) ->
    wf (branch prefix mask left out_right) /\
    forall key,
      get key (branch prefix mask left out_right) =
      match get key (Branch prefix mask left right) with
      | Some value => Some value
      | None => get key operand
      end.
Proof.
  intros A prefix mask left right operand out_right
    Hwl Hwr Hwo Hleft Hright Hoperand [Hwout Hgetout].
  assert (Houtright : all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      out_right).
  { eapply all_keys_of_combine_lookup with
      (left := right) (right := operand) (out := out_right)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - intro key. specialize (Hgetout key).
      destruct (get key right); cbn in Hgetout |- *; exact Hgetout.
    - exact Hright.
    - exact Hoperand. }
  split.
  - now apply branch_wf.
  - intro key. rewrite get_branch by assumption. cbn [get].
    destruct (matches_prefix key prefix mask) eqn:P.
    + destruct (zero_bit key mask) eqn:Z.
      * assert (Eoperand : get key operand = None).
        { eapply all_keys_none; [exact Hoperand|].
          intros [_ Hbit]. rewrite Z in Hbit. discriminate. }
        rewrite Eoperand. now destruct (get key left).
      * apply Hgetout.
    + assert (Eoperand : get key operand = None).
      { eapply all_keys_none; [exact Hoperand|].
        intros [Hprefix _]. rewrite P in Hprefix. discriminate. }
      now rewrite Eoperand.
Qed.

(** Changed-result composition for a left-outer one-bit route. *)
Lemma union_left_specialized_changed_left_outer_right_branch_correct_wf:
  forall (A : Type) prefix mask (left right : t A)
      operand_prefix operand_mask (operand_left operand_right : t A) key,
    wf (Branch prefix mask left right) ->
    wf (Branch operand_prefix operand_mask operand_left operand_right) ->
    (N.eqb mask operand_mask && N.eqb prefix operand_prefix)%bool = false ->
    mask_above mask operand_mask = true ->
    representative (Branch operand_prefix operand_mask operand_left operand_right) = Some key ->
    matches_prefix key prefix mask = true ->
    zero_bit key mask = false ->
    all_keys (fun stored =>
      matches_prefix stored prefix mask = true /\ zero_bit stored mask = false)
      (Branch operand_prefix operand_mask operand_left operand_right) ->
    (wf (union_left_specialized_changed_result right
           (Branch operand_prefix operand_mask operand_left operand_right)) /\
      forall stored,
        get stored (union_left_specialized_changed_result right
          (Branch operand_prefix operand_mask operand_left operand_right)) =
        match get stored right with
        | Some value => Some value
        | None => get stored (Branch operand_prefix operand_mask operand_left operand_right)
        end) ->
    wf (union_left_specialized_changed_result
      (Branch prefix mask left right)
      (Branch operand_prefix operand_mask operand_left operand_right)) /\
    forall stored,
      get stored (union_left_specialized_changed_result
        (Branch prefix mask left right)
        (Branch operand_prefix operand_mask operand_left operand_right)) =
      match get stored (Branch prefix mask left right) with
      | Some value => Some value
      | None => get stored (Branch operand_prefix operand_mask operand_left operand_right)
      end.
Proof.
  intros A prefix mask left right operand_prefix operand_mask operand_left operand_right key
    Houter Hoperand Hsame Habove Hrep Hprefix Hside Hall Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr Hnl Hnr Hleft Hright]; subst.
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Habove, Hrep, Hprefix, Hside.
  destruct (union_left_specialized_changed right
    (Branch operand_prefix operand_mask operand_left operand_right)) eqn:Echild.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild.
    eapply union_left_specialized_left_outer_right_branch_correct_wf; eauto.
  - unfold union_left_specialized_changed_result in Hchild.
    rewrite Echild in Hchild.
    destruct (union_left_specialized_left_outer_right_branch_correct_wf A prefix mask
      left right (Branch operand_prefix operand_mask operand_left operand_right) right
      Hwl Hwr Hoperand Hleft Hright Hall Hchild) as [_ Hget].
    split; [exact Houter|]. intro stored.
    assert (Ebranch : branch prefix mask left right = Branch prefix mask left right).
    { now apply branch_unchanged. }
    rewrite <- Ebranch at 1.
    apply Hget.
Qed.

(** Dual unequal-split reconstruction for the branch traversed by the
    worker's inner recursion. *)
Lemma union_left_specialized_right_outer_left_branch_correct_wf:
  forall (A : Type) prefix mask (operand left right out_left : t A),
    wf operand -> wf left -> wf right ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      operand ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      left ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      right ->
    (wf out_left /\
      forall key,
        get key out_left =
        match get key operand with Some value => Some value | None => get key left end) ->
    wf (branch prefix mask out_left right) /\
    forall key,
      get key (branch prefix mask out_left right) =
      match get key operand with
      | Some value => Some value
      | None => get key (Branch prefix mask left right)
      end.
Proof.
  intros A prefix mask operand left right out_left
    Hwo Hwl Hwr Hoperand Hleft Hright [Hwout Hgetout].
  assert (Houtleft : all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      out_left).
  { eapply all_keys_of_combine_lookup with
      (left := operand) (right := left) (out := out_left)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - intro key. specialize (Hgetout key).
      destruct (get key operand); cbn in Hgetout |- *; exact Hgetout.
    - exact Hoperand.
    - exact Hleft. }
  split.
  - now apply branch_wf.
  - intro key. rewrite get_branch by assumption. cbn [get].
    destruct (matches_prefix key prefix mask) eqn:P.
    + destruct (zero_bit key mask) eqn:Z.
      * apply Hgetout.
      * assert (Eoperand : get key operand = None).
        { eapply all_keys_none; [exact Hoperand|].
          intros [_ Hbit]. rewrite Z in Hbit. discriminate. }
        now rewrite Eoperand.
    + assert (Eoperand : get key operand = None).
      { eapply all_keys_none; [exact Hoperand|].
        intros [Hprefix _]. rewrite P in Hprefix. discriminate. }
      now rewrite Eoperand.
Qed.

Lemma union_left_specialized_right_outer_right_branch_correct_wf:
  forall (A : Type) prefix mask (operand left right out_right : t A),
    wf operand -> wf left -> wf right ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      operand ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = true)
      left ->
    all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      right ->
    (wf out_right /\
      forall key,
        get key out_right =
        match get key operand with Some value => Some value | None => get key right end) ->
    wf (branch prefix mask left out_right) /\
    forall key,
      get key (branch prefix mask left out_right) =
      match get key operand with
      | Some value => Some value
      | None => get key (Branch prefix mask left right)
      end.
Proof.
  intros A prefix mask operand left right out_right
    Hwo Hwl Hwr Hoperand Hleft Hright [Hwout Hgetout].
  assert (Houtright : all_keys
      (fun key => matches_prefix key prefix mask = true /\ zero_bit key mask = false)
      out_right).
  { eapply all_keys_of_combine_lookup with
      (left := operand) (right := right) (out := out_right)
      (f := fun x y => match x with Some _ => x | None => y end).
    - reflexivity.
    - intro key. specialize (Hgetout key).
      destruct (get key operand); cbn in Hgetout |- *; exact Hgetout.
    - exact Hoperand.
    - exact Hright. }
  split.
  - now apply branch_wf.
  - intro key. rewrite get_branch by assumption. cbn [get].
    destruct (matches_prefix key prefix mask) eqn:P.
    + destruct (zero_bit key mask) eqn:Z.
      * assert (Eoperand : get key operand = None).
        { eapply all_keys_none; [exact Hoperand|].
          intros [_ Hbit]. rewrite Z in Hbit. discriminate. }
        rewrite Eoperand. now destruct (get key left).
      * apply Hgetout.
    + assert (Eoperand : get key operand = None).
      { eapply all_keys_none; [exact Hoperand|].
        intros [Hprefix _]. rewrite P in Hprefix. discriminate. }
      now rewrite Eoperand.
Qed.

(** Changed-result composition when the right operand has the outer mask and
    its routed left child is revisited. *)
Lemma union_left_specialized_changed_right_outer_left_branch_correct_wf:
  forall (A : Type) operand_prefix operand_mask (operand_left operand_right : t A)
      prefix mask (left right : t A) key,
    wf (Branch operand_prefix operand_mask operand_left operand_right) ->
    wf (Branch prefix mask left right) ->
    (N.eqb operand_mask mask && N.eqb operand_prefix prefix)%bool = false ->
    mask_above operand_mask mask = false ->
    mask_above mask operand_mask = true ->
    representative (Branch operand_prefix operand_mask operand_left operand_right) = Some key ->
    matches_prefix key prefix mask = true ->
    zero_bit key mask = true ->
    all_keys (fun stored =>
      matches_prefix stored prefix mask = true /\ zero_bit stored mask = true)
      (Branch operand_prefix operand_mask operand_left operand_right) ->
    (wf (union_left_specialized_changed_result
           (Branch operand_prefix operand_mask operand_left operand_right) left) /\
      forall stored,
        get stored (union_left_specialized_changed_result
          (Branch operand_prefix operand_mask operand_left operand_right) left) =
        match get stored (Branch operand_prefix operand_mask operand_left operand_right) with
        | Some value => Some value
        | None => get stored left
        end) ->
    wf (union_left_specialized_changed_result
      (Branch operand_prefix operand_mask operand_left operand_right)
      (Branch prefix mask left right)) /\
    forall stored,
      get stored (union_left_specialized_changed_result
        (Branch operand_prefix operand_mask operand_left operand_right)
        (Branch prefix mask left right)) =
      match get stored (Branch operand_prefix operand_mask operand_left operand_right) with
      | Some value => Some value
      | None => get stored (Branch prefix mask left right)
      end.
Proof.
  intros A operand_prefix operand_mask operand_left operand_right
    prefix mask left right key Hoperand Houter Hsame Hnotabove Habove
    Hrep Hprefix Hside Hall Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr _ _ Hleft Hright]; subst.
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Hnotabove, Habove, Hrep, Hprefix, Hside.
  destruct (union_left_specialized_changed
    (Branch operand_prefix operand_mask operand_left operand_right) left) eqn:Echild;
    unfold union_left_specialized_changed_result in Hchild;
    rewrite Echild in Hchild;
    eapply union_left_specialized_right_outer_left_branch_correct_wf; eauto.
Qed.

(** Changed-result composition for the one-bit child of an outer right branch. *)
Lemma union_left_specialized_changed_right_outer_right_branch_correct_wf:
  forall (A : Type) operand_prefix operand_mask (operand_left operand_right : t A)
      prefix mask (left right : t A) key,
    wf (Branch operand_prefix operand_mask operand_left operand_right) ->
    wf (Branch prefix mask left right) ->
    (N.eqb operand_mask mask && N.eqb operand_prefix prefix)%bool = false ->
    mask_above operand_mask mask = false ->
    mask_above mask operand_mask = true ->
    representative (Branch operand_prefix operand_mask operand_left operand_right) = Some key ->
    matches_prefix key prefix mask = true ->
    zero_bit key mask = false ->
    all_keys (fun stored =>
      matches_prefix stored prefix mask = true /\ zero_bit stored mask = false)
      (Branch operand_prefix operand_mask operand_left operand_right) ->
    (wf (union_left_specialized_changed_result
           (Branch operand_prefix operand_mask operand_left operand_right) right) /\
      forall stored,
        get stored (union_left_specialized_changed_result
          (Branch operand_prefix operand_mask operand_left operand_right) right) =
        match get stored (Branch operand_prefix operand_mask operand_left operand_right) with
        | Some value => Some value
        | None => get stored right
        end) ->
    wf (union_left_specialized_changed_result
      (Branch operand_prefix operand_mask operand_left operand_right)
      (Branch prefix mask left right)) /\
    forall stored,
      get stored (union_left_specialized_changed_result
        (Branch operand_prefix operand_mask operand_left operand_right)
        (Branch prefix mask left right)) =
      match get stored (Branch operand_prefix operand_mask operand_left operand_right) with
      | Some value => Some value
      | None => get stored (Branch prefix mask left right)
      end.
Proof.
  intros A operand_prefix operand_mask operand_left operand_right
    prefix mask left right key Hoperand Houter Hsame Hnotabove Habove
    Hrep Hprefix Hside Hall Hchild.
  inversion Houter as [| |? ? ? ? Hwl Hwr _ _ Hleft Hright]; subst.
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Hnotabove, Habove, Hrep, Hprefix, Hside.
  destruct (union_left_specialized_changed
    (Branch operand_prefix operand_mask operand_left operand_right) right) eqn:Echild;
    unfold union_left_specialized_changed_result in Hchild;
    rewrite Echild in Hchild;
    eapply union_left_specialized_right_outer_right_branch_correct_wf; eauto.
Qed.

(** Package the common precondition of [join_disjoint_correct] for the
    terminal branch/branch cases of the specialized worker. *)
Lemma union_left_specialized_join_branches_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    wf (Branch pa ma la ra) ->
    wf (Branch pb mb lb rb) ->
    (forall ka va kb vb,
      get ka (Branch pa ma la ra) = Some va ->
      get kb (Branch pb mb lb rb) = Some vb ->
      (ma < highest_differing_bit ka kb)%N /\
      (mb < highest_differing_bit ka kb)%N) ->
    wf (join (Branch pa ma la ra) (Branch pb mb lb rb)) /\
    forall key,
      get key (join (Branch pa ma la ra) (Branch pb mb lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value
      | None => get key (Branch pb mb lb rb)
      end.
Proof.
  intros A pa ma la ra pb mb lb rb Hwa Hwb Hseparated.
  inversion Hwa as [| |? ? ? ? _ _ _ _ Hla Hra]; subst.
  inversion Hwb as [| |? ? ? ? _ _ _ _ Hlb Hrb]; subst.
  eapply join_disjoint_correct; eauto.
  - now apply branch_all_prefix.
  - now apply branch_all_prefix.
Qed.

(** Equal split positions with different prefixes are disjoint at a bit
    strictly above the shared split. *)
Lemma union_left_specialized_same_mask_disjoint_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb (lb rb : t A),
    wf (Branch pa ma la ra) ->
    wf (Branch pb ma lb rb) ->
    pa <> pb ->
    wf (join (Branch pa ma la ra) (Branch pb ma lb rb)) /\
    forall key,
      get key (join (Branch pa ma la ra) (Branch pb ma lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value
      | None => get key (Branch pb ma lb rb)
      end.
Proof.
  intros A pa ma la ra pb lb rb Hwa Hwb Hprefix.
  inversion Hwa as [| |? ? ? ? _ _ _ _ Hla Hra]; subst.
  inversion Hwb as [| |? ? ? ? _ _ _ _ Hlb Hrb]; subst.
  apply union_left_specialized_join_branches_correct_wf; auto.
  intros ka va kb vb Hka Hkb.
  assert (Hpa : matches_prefix ka pa ma = true).
  { apply (@branch_all_prefix A pa ma la ra Hla Hra) with va; exact Hka. }
  assert (Hpb : matches_prefix kb pb ma = true).
  { apply (@branch_all_prefix A pb ma lb rb Hlb Hrb) with vb; exact Hkb. }
  assert (Hdifferent : prefix ka ma <> prefix kb ma).
  { unfold matches_prefix in Hpa, Hpb.
    apply N.eqb_eq in Hpa. apply N.eqb_eq in Hpb.
    intro E. apply Hprefix. now rewrite <- Hpa, E, Hpb. }
  pose proof (prefix_mismatch_highest_above ka kb ma Hdifferent) as Hhigh.
  split; exact Hhigh.
Qed.

(** Equal masks with distinct prefixes take the terminal join path as well. *)
Lemma union_left_specialized_changed_same_mask_disjoint_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    wf (Branch pa ma la ra) -> wf (Branch pb mb lb rb) ->
    (N.eqb ma mb && N.eqb pa pb)%bool = false ->
    mask_above ma mb = false -> mask_above mb ma = false ->
    wf (union_left_specialized_changed_result
      (Branch pa ma la ra) (Branch pb mb lb rb)) /\
    forall key, get key (union_left_specialized_changed_result
      (Branch pa ma la ra) (Branch pb mb lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value | None => get key (Branch pb mb lb rb) end.
Proof.
  intros A pa ma la ra pb mb lb rb Hwa Hwb Hsame Hab Hba.
  assert (Emasks : ma = mb) by
    (apply N.le_antisymm; apply N.ltb_ge; assumption).
  subst mb.
  assert (Eprefix : pa <> pb).
  { intro Eprefix. subst pb. now rewrite !N.eqb_refl in Hsame. }
  destruct (union_left_specialized_same_mask_disjoint_correct_wf A pa ma la ra
    pb lb rb Hwa Hwb Eprefix) as [Hwf Hget].
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Hab. exact (conj Hwf Hget).
Qed.

(** If the right root is deeper and its representative misses the left
    root's prefix, every pair of bindings differs above both root masks. *)
Lemma union_left_specialized_left_outer_disjoint_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A) kb,
    wf (Branch pa ma la ra) ->
    wf (Branch pb mb lb rb) ->
    (mb < ma)%N ->
    representative (Branch pb mb lb rb) = Some kb ->
    matches_prefix kb pa ma = false ->
    wf (join (Branch pa ma la ra) (Branch pb mb lb rb)) /\
    forall key,
      get key (join (Branch pa ma la ra) (Branch pb mb lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value
      | None => get key (Branch pb mb lb rb)
      end.
Proof.
  intros A pa ma la ra pb mb lb rb kb Hwa Hwb Hm Hrep Hmiss.
  inversion Hwa as [| |? ? ? ? _ _ _ _ Hla Hra]; subst.
  inversion Hwb as [| |? ? ? ? _ _ _ _ Hlb Hrb]; subst.
  assert (Hpa : all_keys (fun k => matches_prefix k pa ma = true)
    (Branch pa ma la ra)) by (now apply branch_all_prefix).
  assert (Hpb : all_keys (fun k => matches_prefix k pb mb = true)
    (Branch pb mb lb rb)) by (now apply branch_all_prefix).
  destruct (representative_get_wf Hwb Hrep) as [value Hgetrep].
  assert (Hkb : get kb (Branch pb mb lb rb) <> None) by
    (rewrite Hgetrep; discriminate).
  pose proof (@all_keys_uniform_above A (Branch pb mb lb rb)
    pb mb kb ma Hpb Hm Hkb) as Hright.
  apply union_left_specialized_join_branches_correct_wf; auto.
  intros ka va kr vr Hka Hkr.
  assert (Hleft_prefix : matches_prefix ka pa ma = true).
  { exact (Hpa ka va Hka). }
  specialize (Hright kr vr Hkr) as [Hright_prefix _].
  assert (Hdifferent : prefix ka ma <> prefix kr ma).
  { unfold matches_prefix in Hleft_prefix, Hright_prefix, Hmiss.
    apply N.eqb_eq in Hleft_prefix. apply N.eqb_eq in Hright_prefix.
    apply N.eqb_neq in Hmiss.
    intro E. apply Hmiss. now rewrite <- Hleft_prefix, E, Hright_prefix. }
  pose proof (prefix_mismatch_highest_above ka kr ma Hdifferent) as Hhigh.
  split; [exact Hhigh|lia].
Qed.

(** Symmetric terminal case: the left root is deeper and misses the right
    root's prefix. *)
Lemma union_left_specialized_right_outer_disjoint_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A) ka,
    wf (Branch pa ma la ra) ->
    wf (Branch pb mb lb rb) ->
    (ma < mb)%N ->
    representative (Branch pa ma la ra) = Some ka ->
    matches_prefix ka pb mb = false ->
    wf (join (Branch pa ma la ra) (Branch pb mb lb rb)) /\
    forall key,
      get key (join (Branch pa ma la ra) (Branch pb mb lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value
      | None => get key (Branch pb mb lb rb)
      end.
Proof.
  intros A pa ma la ra pb mb lb rb ka Hwa Hwb Hm Hrep Hmiss.
  inversion Hwa as [| |? ? ? ? _ _ _ _ Hla Hra]; subst.
  inversion Hwb as [| |? ? ? ? _ _ _ _ Hlb Hrb]; subst.
  assert (Hpa : all_keys (fun k => matches_prefix k pa ma = true)
    (Branch pa ma la ra)) by (now apply branch_all_prefix).
  assert (Hpb : all_keys (fun k => matches_prefix k pb mb = true)
    (Branch pb mb lb rb)) by (now apply branch_all_prefix).
  destruct (representative_get_wf Hwa Hrep) as [value Hgetrep].
  assert (Hka : get ka (Branch pa ma la ra) <> None) by
    (rewrite Hgetrep; discriminate).
  pose proof (@all_keys_uniform_above A (Branch pa ma la ra)
    pa ma ka mb Hpa Hm Hka) as Hleft.
  apply union_left_specialized_join_branches_correct_wf; auto.
  intros kl vl kb vb Hkl Hkb.
  specialize (Hleft kl vl Hkl) as [Hleft_prefix _].
  assert (Hright_prefix : matches_prefix kb pb mb = true).
  { exact (Hpb kb vb Hkb). }
  assert (Hdifferent : prefix kl mb <> prefix kb mb).
  { unfold matches_prefix in Hleft_prefix, Hright_prefix, Hmiss.
    apply N.eqb_eq in Hleft_prefix. apply N.eqb_eq in Hright_prefix.
    apply N.eqb_neq in Hmiss.
    intro E. apply Hmiss. now rewrite <- Hleft_prefix, E, Hright_prefix. }
  pose proof (prefix_mismatch_highest_above kl kb mb Hdifferent) as Hhigh.
  split; [lia|exact Hhigh].
Qed.

(** A failed outer-prefix test is a changed result carrying the established
    separated join, rather than an unchanged certificate. *)
Lemma union_left_specialized_changed_left_outer_disjoint_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A) kb,
    wf (Branch pa ma la ra) ->
    wf (Branch pb mb lb rb) ->
    (N.eqb ma mb && N.eqb pa pb)%bool = false ->
    mask_above ma mb = true ->
    representative (Branch pb mb lb rb) = Some kb ->
    matches_prefix kb pa ma = false ->
    wf (union_left_specialized_changed_result
      (Branch pa ma la ra) (Branch pb mb lb rb)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch pa ma la ra) (Branch pb mb lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value
      | None => get key (Branch pb mb lb rb)
      end.
Proof.
  intros A pa ma la ra pb mb lb rb kb Hwa Hwb Hsame Habove Hrep Hmiss.
  assert (Hlt : (mb < ma)%N) by (apply mask_above_spec; exact Habove).
  destruct (union_left_specialized_left_outer_disjoint_correct_wf A pa ma la ra
    pb mb lb rb kb Hwa Hwb Hlt Hrep Hmiss) as [Hwf Hget].
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Habove, Hrep, Hmiss. exact (conj Hwf Hget).
Qed.

(** Symmetric terminal signal case when the left root is deeper. *)
Lemma union_left_specialized_changed_right_outer_disjoint_correct_wf:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A) ka,
    wf (Branch pa ma la ra) ->
    wf (Branch pb mb lb rb) ->
    (N.eqb ma mb && N.eqb pa pb)%bool = false ->
    mask_above ma mb = false ->
    mask_above mb ma = true ->
    representative (Branch pa ma la ra) = Some ka ->
    matches_prefix ka pb mb = false ->
    wf (union_left_specialized_changed_result
      (Branch pa ma la ra) (Branch pb mb lb rb)) /\
    forall key,
      get key (union_left_specialized_changed_result
        (Branch pa ma la ra) (Branch pb mb lb rb)) =
      match get key (Branch pa ma la ra) with
      | Some value => Some value
      | None => get key (Branch pb mb lb rb)
      end.
Proof.
  intros A pa ma la ra pb mb lb rb ka Hwa Hwb Hsame Hnotabove Habove Hrep Hmiss.
  assert (Hlt : (ma < mb)%N) by (apply mask_above_spec; exact Habove).
  destruct (union_left_specialized_right_outer_disjoint_correct_wf A pa ma la ra
    pb mb lb rb ka Hwa Hwb Hlt Hrep Hmiss) as [Hwf Hget].
  unfold union_left_specialized_changed_result.
  rewrite union_left_specialized_changed_equation.
  rewrite Hsame, Hnotabove, Habove, Hrep, Hmiss. exact (conj Hwf Hget).
Qed.

(** Every recursive pair selected by the nested worker is smaller in the
    combined structural size.  The final correctness theorem uses this as its
    well-founded induction measure, independently of routing outcomes. *)
Lemma union_left_specialized_branch_calls_smaller:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    size la + size lb < size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size ra + size rb < size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size la + size (Branch pb mb lb rb) <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size ra + size (Branch pb mb lb rb) <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size (Branch pa ma la ra) + size lb <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size (Branch pa ma la ra) + size rb <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb).
Proof. intros. cbn [size]. lia. Qed.

(** Final well-founded assembly for the integer specialized worker. *)
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
        |left_prefix left_mask left_left left_right];
      destruct right as [|right_key right_value
        |right_prefix right_mask right_left right_right].
    - split; [constructor|]. intro key. reflexivity.
    - split; [exact Hwr|]. intro key. reflexivity.
    - split; [exact Hwr|]. intro key. reflexivity.
    - split; [exact Hwl|]. intro key.
      rewrite union_left_specialized_equation. cbn.
      destruct (Pos.eqb key left_key); reflexivity.
    - now apply union_left_specialized_leaf_left_correct_wf.
    - now apply union_left_specialized_leaf_left_correct_wf.
    - split; [exact Hwl|]. intro key.
      rewrite union_left_specialized_equation.
      change (get key (Branch left_prefix left_mask left_left left_right) =
        match get key (Branch left_prefix left_mask left_left left_right) with
        | Some value => Some value
        | None => None
        end).
      destruct (get key (Branch left_prefix left_mask left_left left_right)); reflexivity.
    - now apply union_left_specialized_leaf_right_correct_wf.
    - inversion Hwl as
        [| |? ? ? ? Hwall Hwarr Hnall Hnalr Hall Har]; subst.
      inversion Hwr as
        [| |? ? ? ? Hwbrl Hwbrr Hnbrl Hnbrr Hbl Hbr]; subst.
      rewrite union_left_specialized_equation.
      destruct (N.eqb left_mask right_mask && N.eqb left_prefix right_prefix)%bool
        eqn:Same.
      + apply Bool.andb_true_iff in Same. destruct Same as [Em Ep].
        apply N.eqb_eq in Em. apply N.eqb_eq in Ep.
        subst right_mask right_prefix.
        destruct (H (size left_left + size right_left)
          ltac:(cbn [size]; lia) left_left right_left eq_refl Hwall Hwbrl)
          as [Hwoutl Hgetoutl].
        destruct (H (size left_right + size right_right)
          ltac:(cbn [size]; lia) left_right right_right eq_refl Hwarr Hwbrr)
          as [Hwoutr Hgetoutr].
        eapply union_left_specialized_same_branch_correct_wf; eauto.
      + destruct (mask_above left_mask right_mask) eqn:Mab.
        * apply mask_above_spec in Mab.
          destruct (representative right_left) as [right_rep|] eqn:Rb.
          -- assert (Hrepb : representative
                (Branch right_prefix right_mask right_left right_right) = Some right_rep).
             { cbn [representative]. now rewrite Rb. }
             assert (Hbprefix : all_keys
                 (fun key => matches_prefix key right_prefix right_mask = true)
                 (Branch right_prefix right_mask right_left right_right)) by
               (now apply branch_all_prefix).
             destruct (representative_get_wf Hwr Hrepb) as [right_value Hgetrep].
             assert (Hrepnot : get right_rep
                 (Branch right_prefix right_mask right_left right_right) <> None) by
               (rewrite Hgetrep; discriminate).
             pose proof (@all_keys_uniform_above A
               (Branch right_prefix right_mask right_left right_right)
               right_prefix right_mask right_rep left_mask Hbprefix Mab Hrepnot)
               as Houter0.
             destruct (matches_prefix right_rep left_prefix left_mask) eqn:Eprefix.
             ++ assert (Hoperand : all_keys (fun key =>
                    matches_prefix key left_prefix left_mask = true /\
                    zero_bit key left_mask = zero_bit right_rep left_mask)
                    (Branch right_prefix right_mask right_left right_right)).
                { intros key value Hget. specialize (Houter0 _ _ Hget) as [P Z].
                  split; [|exact Z]. unfold matches_prefix in P, Eprefix |- *.
                  apply N.eqb_eq in P. apply N.eqb_eq in Eprefix.
                  apply N.eqb_eq. congruence. }
                destruct (zero_bit right_rep left_mask) eqn:Eside.
                ** destruct (H (size left_left +
                      size (Branch right_prefix right_mask right_left right_right))
                    ltac:(cbn [size]; lia) left_left
                   (Branch right_prefix right_mask right_left right_right)
                    eq_refl Hwall Hwr) as [Hwout Hgetout].
                   rewrite Hrepb, Eprefix, Eside.
                   eapply union_left_specialized_left_outer_branch_correct_wf
                     with (operand := Branch right_prefix right_mask right_left right_right);
                     eauto.
                ** destruct (H (size left_right +
                      size (Branch right_prefix right_mask right_left right_right))
                    ltac:(cbn [size]; lia) left_right
                    (Branch right_prefix right_mask right_left right_right)
                    eq_refl Hwarr Hwr) as [Hwout Hgetout].
                   rewrite Hrepb, Eprefix, Eside.
                   eapply union_left_specialized_left_outer_right_branch_correct_wf
                     with (operand := Branch right_prefix right_mask right_left right_right);
                     eauto.
             ++ rewrite Hrepb, Eprefix.
                eapply union_left_specialized_left_outer_disjoint_correct_wf;
                  eauto.
          -- apply (representative_none_wf Hwbrl) in Rb. subst right_left.
             destruct Hnbrl as [key [value Efound]]. discriminate.
        * destruct (mask_above right_mask left_mask) eqn:Mba.
          -- apply mask_above_spec in Mba.
             destruct (representative left_left) as [left_rep|] eqn:Ra.
             ++ assert (Hrepa : representative
                   (Branch left_prefix left_mask left_left left_right) = Some left_rep).
                { cbn [representative]. now rewrite Ra. }
                assert (Haprefix : all_keys
                    (fun key => matches_prefix key left_prefix left_mask = true)
                    (Branch left_prefix left_mask left_left left_right)) by
                  (now apply branch_all_prefix).
                destruct (representative_get_wf Hwl Hrepa) as [left_value Hgetrep].
                assert (Hrepnot : get left_rep
                    (Branch left_prefix left_mask left_left left_right) <> None) by
                  (rewrite Hgetrep; discriminate).
                pose proof (@all_keys_uniform_above A
                  (Branch left_prefix left_mask left_left left_right)
                  left_prefix left_mask left_rep right_mask Haprefix Mba Hrepnot)
                  as Houter0.
                destruct (matches_prefix left_rep right_prefix right_mask) eqn:Eprefix.
                ** assert (Hoperand : all_keys (fun key =>
                       matches_prefix key right_prefix right_mask = true /\
                       zero_bit key right_mask = zero_bit left_rep right_mask)
                       (Branch left_prefix left_mask left_left left_right)).
                   { intros key value Hget. specialize (Houter0 _ _ Hget) as [P Z].
                     split; [|exact Z]. unfold matches_prefix in P, Eprefix |- *.
                     apply N.eqb_eq in P. apply N.eqb_eq in Eprefix.
                     apply N.eqb_eq. congruence. }
                   destruct (zero_bit left_rep right_mask) eqn:Eside.
                   --- destruct (H (size (Branch left_prefix left_mask left_left left_right) +
                         size right_left) ltac:(cbn [size]; lia)
                       (Branch left_prefix left_mask left_left left_right) right_left
                       eq_refl Hwl Hwbrl) as [Hwout Hgetout].
                       rewrite Hrepa, Eprefix, Eside.
                       eapply union_left_specialized_right_outer_left_branch_correct_wf
                         with (operand := Branch left_prefix left_mask left_left left_right);
                         eauto.
                   --- destruct (H (size (Branch left_prefix left_mask left_left left_right) +
                         size right_right) ltac:(cbn [size]; lia)
                       (Branch left_prefix left_mask left_left left_right) right_right
                       eq_refl Hwl Hwbrr) as [Hwout Hgetout].
                       rewrite Hrepa, Eprefix, Eside.
                       eapply union_left_specialized_right_outer_right_branch_correct_wf
                         with (operand := Branch left_prefix left_mask left_left left_right);
                         eauto.
                ** rewrite Hrepa, Eprefix.
                   eapply union_left_specialized_right_outer_disjoint_correct_wf;
                     eauto.
             ++ apply (representative_none_wf Hwall) in Ra. subst left_left.
                destruct Hnall as [key [value Efound]]. discriminate.
          -- assert (Emasks : left_mask = right_mask) by
               (apply N.le_antisymm; apply N.ltb_ge; assumption).
             subst right_mask.
             assert (Eprefix : left_prefix <> right_prefix).
             { intro Eprefix. subst right_prefix.
               now rewrite !N.eqb_refl in Same. }
             eapply union_left_specialized_same_mask_disjoint_correct_wf;
               eauto.
  }
  intros left right Hwl Hwr.
  eapply Hstrong with (total := size left + size right); eauto.
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
