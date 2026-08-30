(** Focused certificates and refinement proof workspace for
    [PatriciaUnion].  Recompiling this file reuses the cached core proof. *)

From Stdlib Require Import Bool NArith.
Require Import PatriciaBits Patricia PatriciaProof PatriciaUnion.

Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros A left. destruct left; reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. reflexivity. Qed.

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
