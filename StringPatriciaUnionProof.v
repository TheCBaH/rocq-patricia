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
