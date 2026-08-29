From Stdlib Require Import Arith.Wf_nat Bool Lia List PeanoNat Sorting.Sorted
  Strings.String.
Import ListNotations.

Require Import StringBits StringPatricia.

Lemma get_empty:
  forall (A : Type) key, @get A key empty = None.
Proof. reflexivity. Qed.

Lemma get_singleton_same:
  forall (A : Type) key (value : A), get key (singleton key value) = Some value.
Proof.
  intros. cbn [get singleton]. now rewrite String.eqb_refl.
Qed.

Lemma get_singleton_other:
  forall (A : Type) lkey rkey (value : A),
    lkey <> rkey -> get lkey (singleton rkey value) = None.
Proof.
  intros. cbn [get singleton]. apply String.eqb_neq in H. now rewrite H.
Qed.

Lemma mem_get:
  forall (A : Type) key (m : t A),
    mem key m = match get key m with Some _ => true | None => false end.
Proof.
  intros A key m.
  induction m as [|stored value|sample split ltree IHl rtree IHr]; cbn.
  - reflexivity.
  - now destruct (String.eqb key stored).
  - now destruct (bit_at key split).
Qed.

Lemma mem_spec:
  forall (A : Type) key (m : t A),
    mem key m = true <-> exists value, get key m = Some value.
Proof.
  intros A key m. rewrite mem_get. destruct (get key m) eqn:E; split; intros H.
  - now exists a.
  - split; intros; reflexivity.
  - discriminate.
  - destruct H as [value H]. congruence.
Qed.

Lemma is_empty_spec:
  forall (A : Type) (m : t A), is_empty m = true <-> m = Empty.
Proof.
  intros A m. destruct m as [|key value|sample split ltree rtree]; cbn.
  - split; intros H; reflexivity.
  - split; [discriminate|intros H; discriminate].
  - split; [discriminate|intros H; discriminate].
Qed.

Lemma get_map:
  forall (A B : Type) (f : string -> A -> B) key (m : t A),
    get key (map f m) = option_map (f key) (get key m).
Proof.
  intros A B f key m. induction m as [|stored value|sample split ltree IHl rtree IHr]; cbn.
  - reflexivity.
  - destruct (String.eqb key stored) eqn:E; cbn.
    + apply String.eqb_eq in E. now subst.
    + reflexivity.
  - destruct (bit_at key split); assumption.
Qed.

Lemma elements_aux_spec:
  forall (A : Type) (m : t A) tail,
    elements_aux m tail = elements m ++ tail.
Proof.
  intros A m.
  induction m as [|key value|sample split ltree IHl rtree IHr];
    intros tail; cbn [elements].
  - reflexivity.
  - reflexivity.
  - change (elements_aux ltree (elements_aux rtree tail) =
      elements_aux ltree (elements_aux rtree []) ++ tail).
    rewrite !IHl, !IHr.
    now rewrite List.app_nil_r, List.app_assoc.
Qed.

Lemma elements_branch:
  forall (A : Type) sample split (ltree rtree : t A),
    elements (Branch sample split ltree rtree) =
      elements ltree ++ elements rtree.
Proof.
  intros. change (elements_aux ltree (elements_aux rtree []) =
    elements ltree ++ elements rtree).
  rewrite elements_aux_spec, elements_aux_spec.
  now rewrite List.app_nil_r.
Qed.

Lemma fold_elements:
  forall (A B : Type) (f : B -> string -> A -> B) (m : t A) acc,
    fold f m acc =
    List.fold_left (fun state kv => f state (fst kv) (snd kv)) (elements m) acc.
Proof.
  intros A B f m. induction m as [|key value|sample split ltree IHl rtree IHr];
    intros acc.
  - reflexivity.
  - reflexivity.
  - cbn [fold]. rewrite elements_branch, List.fold_left_app.
    now rewrite <- IHl, <- IHr.
Qed.

(** A well-formed branch separates all keys in its left and right subtrees at
    [split], and every key below it shares the sample's preceding bits. *)

Fixpoint all_keys {A : Type} (P : string -> Prop) (m : t A) : Prop :=
  match m with
  | Empty => True
  | Leaf key _ => P key
  | Branch _ _ ltree rtree => all_keys P ltree /\ all_keys P rtree
  end.

Definition same_prefix (sample key : string) (split : nat) : Prop :=
  forall n, n < split -> bit_at sample n = bit_at key n.

(** The strict order observed by a left-before-right Patricia traversal is
    lexicographic order on the prefix-free logical bit view: at the first
    differing position, the left key has [false] and the right key has
    [true]. *)
Definition bit_lex_lt (left right : string) : Prop :=
  exists split,
    first_diff left right = Some split /\
    bit_at left split = false /\
    bit_at right split = true.

(** The scanner specification gives the forward direction (a reported split
    is first).  This converse packages the form used by traversal and merge:
    agreement below a split and disagreement at it force that exact split. *)
Lemma first_diff_at:
  forall left right split,
    same_prefix left right split ->
    bit_at left split <> bit_at right split ->
    first_diff left right = Some split.
Proof.
  intros left right split Hprefix Hbit.
  assert (Hneq : left <> right).
  { intro E. subst right. apply Hbit. reflexivity. }
  destruct (first_diff_unequal_exists left right Hneq) as [differing Hdiff].
  destruct (first_diff_spec _ _ _ Hdiff) as [Hdifferent Hbefore].
  assert (Hle : differing <= split).
  { apply Nat.nlt_ge. intro Hgt. apply Hbit. apply Hbefore. exact Hgt. }
  assert (Hge : split <= differing).
  { apply Nat.nlt_ge. intro Hlt. apply Hdifferent. apply Hprefix. exact Hlt. }
  assert (differing = split) by lia. subst differing. exact Hdiff.
Qed.

Inductive wf {A : Type} : t A -> Prop :=
| wf_empty : wf Empty
| wf_leaf : forall key value, wf (Leaf key value)
| wf_branch : forall sample split ltree rtree,
    wf ltree ->
    wf rtree ->
    representative ltree <> None ->
    representative rtree <> None ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) ltree ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) rtree ->
    wf (Branch sample split ltree rtree).

Fixpoint splits_after {A : Type} (bound : nat) (m : t A) : Prop :=
  match m with
  | Empty | Leaf _ _ => True
  | Branch _ split ltree rtree =>
      bound < split /\ splits_after bound ltree /\ splits_after bound rtree
  end.

Fixpoint splits_ordered {A : Type} (m : t A) : Prop :=
  match m with
  | Empty | Leaf _ _ => True
  | Branch _ split ltree rtree =>
      splits_after split ltree /\ splits_after split rtree /\
      splits_ordered ltree /\ splits_ordered rtree
  end.

Lemma all_keys_impl:
  forall (A : Type) (P Q : string -> Prop) (m : t A),
    all_keys P m -> (forall key, P key -> Q key) -> all_keys Q m.
Proof.
  intros A P Q m. induction m as [|key value|sample split ltree IHl rtree IHr];
    cbn; intros H HPQ.
  - exact I.
  - now apply HPQ.
  - destruct H. split; [eapply IHl|eapply IHr]; eauto.
Qed.

Lemma all_keys_elements:
  forall (A : Type) (P : string -> Prop) (m : t A),
    all_keys P m <-> forall key value, In (key, value) (elements m) -> P key.
Proof.
  intros A P m. induction m as [|key value|sample split ltree IHl rtree IHr].
  - cbn [all_keys elements elements_aux].
    split; intros; [contradiction|exact I].
  - split.
    + cbn [all_keys elements elements_aux].
      intros H k v [E|Hnone]; [inversion E; subst; assumption|contradiction].
    + intros H. apply (H key value). now left.
  - cbn [all_keys]. rewrite elements_branch. split.
    + intros [Hl Hr] key value Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin|Hin].
      * apply (proj1 IHl Hl key value Hin).
      * apply (proj1 IHr Hr key value Hin).
    + intros H. split.
      * apply (proj2 IHl). intros key value Hin. apply (H key value).
        apply in_or_app. now left.
      * apply (proj2 IHr). intros key value Hin. apply (H key value).
        apply in_or_app. now right.
Qed.

Lemma representative_elements:
  forall (A : Type) (m : t A) key,
    representative m = Some key -> exists value, In (key, value) (elements m).
Proof.
  intros A m. induction m as [|stored value|sample split ltree IHl rtree IHr];
    intros key H.
  - discriminate.
  - cbn [representative] in H. inversion H; subst.
    exists value. cbn [elements elements_aux]. now left.
  - cbn [representative] in H. rewrite elements_branch.
    destruct (representative ltree) eqn:El.
    + inversion H; subst. destruct (IHl _ eq_refl) as [value Hin].
      exists value. apply in_or_app. now left.
    + destruct (IHr _ H) as [value Hin].
      exists value. apply in_or_app. now right.
Qed.

Lemma representative_none_elements:
  forall (A : Type) (m : t A),
    representative m = None <-> elements m = [].
Proof.
  intros A m. induction m as [|key value|sample split ltree IHl rtree IHr].
  - cbn [representative elements elements_aux]. split; intros; reflexivity.
  - cbn [representative elements elements_aux]. split; discriminate.
  - cbn [representative]. rewrite elements_branch.
    destruct (representative ltree) eqn:El.
    + split; [discriminate|]. intros H.
      apply app_eq_nil in H. destruct H as [Hl _].
      apply representative_elements in El. destruct El as [value Hin].
      rewrite Hl in Hin. contradiction.
    + rewrite IHr. split.
      * intros Hr. rewrite (proj1 IHl eq_refl), Hr. reflexivity.
      * intros H. apply app_eq_nil in H. tauto.
Qed.

Lemma get_elements_sound:
  forall (A : Type) (m : t A) key value,
    get key m = Some value -> In (key, value) (elements m).
Proof.
  intros A m. induction m as [|stored stored_value|sample split ltree IHl rtree IHr];
    intros key value H.
  - discriminate.
  - cbn [get elements elements_aux] in *.
    destruct (String.eqb key stored) eqn:E; [|discriminate].
    apply String.eqb_eq in E. inversion H. subst. now left.
  - cbn [get] in H. rewrite elements_branch.
    destruct (bit_at key split) eqn:E.
    + apply in_or_app. right. eapply IHr. exact H.
    + apply in_or_app. left. eapply IHl. exact H.
Qed.

Lemma wf_elements_complete:
  forall (A : Type) (m : t A),
    wf m -> forall key value,
      In (key, value) (elements m) -> get key m = Some value.
Proof.
  intros A m Hwf. induction Hwf as
      [|stored stored_value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros key value Hin.
  - cbn [elements elements_aux] in Hin. contradiction.
  - cbn [elements elements_aux] in Hin.
    destruct Hin as [E|Hnone]; [|contradiction]. inversion E; subst.
    cbn [get]. now rewrite String.eqb_refl.
  - rewrite elements_branch in Hin. cbn [get].
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + pose proof (proj1 (all_keys_elements _ _ _) Hl key value Hin) as [_ Hbit].
      rewrite Hbit. now apply IHl.
    + pose proof (proj1 (all_keys_elements _ _ _) Hr key value Hin) as [_ Hbit].
      rewrite Hbit. now apply IHr.
Qed.

Theorem wf_elements_spec:
  forall (A : Type) (m : t A),
    wf m -> forall key value,
      get key m = Some value <-> In (key, value) (elements m).
Proof.
  intros A m Hwf key value. split.
  - apply get_elements_sound.
  - apply (wf_elements_complete A m Hwf).
Qed.

Lemma StronglySorted_app_cross:
  forall (A : Type) (R : A -> A -> Prop) (left right : list A),
    StronglySorted R left ->
    StronglySorted R right ->
    (forall x y, In x left -> In y right -> R x y) ->
    StronglySorted R (left ++ right).
Proof.
  intros A R left right Hleft.
  induction Hleft as [|x left Hsorted IH Hbefore]; intros Hright Hcross.
  - exact Hright.
  - cbn. constructor.
    + apply IH; [exact Hright|].
      intros a b Ha Hb. apply Hcross; [now right|exact Hb].
    + apply Forall_app. split; [exact Hbefore|].
      apply Forall_forall. intros y Hy. apply Hcross; [now left|exact Hy].
Qed.

Theorem wf_elements_bit_lex_sorted:
  forall (A : Type) (m : t A),
    wf m -> StronglySorted bit_lex_lt (List.map fst (elements m)).
Proof.
  intros A m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr].
  - cbn [elements elements_aux]. constructor.
  - cbn [elements elements_aux]. constructor; constructor.
  - rewrite elements_branch, List.map_app.
    apply StronglySorted_app_cross; [exact IHl|exact IHr|].
    intros left_key right_key Hleft Hright.
    apply in_map_iff in Hleft.
    destruct Hleft as [[stored_left value_left] [Eleft Hinleft]].
    apply in_map_iff in Hright.
    destruct Hright as [[stored_right value_right] [Eright Hinright]].
    cbn in Eleft, Eright. subst stored_left stored_right.
    pose proof (proj1 (all_keys_elements _ _ _) Hl
      left_key value_left Hinleft) as [Hleft_prefix Hleft_bit].
    pose proof (proj1 (all_keys_elements _ _ _) Hr
      right_key value_right Hinright) as [Hright_prefix Hright_bit].
    exists split. split.
    + apply first_diff_at.
      * intros n Hn.
        rewrite <- (Hleft_prefix n Hn), <- (Hright_prefix n Hn).
        reflexivity.
      * rewrite Hleft_bit, Hright_bit. discriminate.
    + now split.
Qed.

Lemma routed_key_elements:
  forall (A : Type) (m : t A) probe stored,
    routed_key probe m = Some stored ->
    exists value, In (stored, value) (elements m).
Proof.
  intros A m. induction m as [|key value|sample split ltree IHl rtree IHr];
    intros probe stored H.
  - discriminate.
  - cbn [routed_key] in H. inversion H; subst.
    exists value. cbn [elements elements_aux]. now left.
  - cbn [routed_key] in H. rewrite elements_branch.
    destruct (bit_at probe split).
    + destruct (IHr _ _ H) as [value Hin]. exists value.
      apply in_or_app. now right.
    + destruct (IHl _ _ H) as [value Hin]. exists value.
      apply in_or_app. now left.
Qed.

Corollary wf_routed_key_get:
  forall (A : Type) (m : t A) probe stored,
    wf m -> routed_key probe m = Some stored ->
    exists value, get stored m = Some value.
Proof.
  intros A m probe stored Hwf Hrouted.
  destruct (routed_key_elements A m probe stored Hrouted) as [value Hin].
  exists value. now apply (wf_elements_complete A m Hwf).
Qed.

Lemma wf_elements_keys_nodup:
  forall (A : Type) (m : t A),
    wf m -> NoDup (List.map fst (elements m)).
Proof.
  intros A m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr].
  - cbn [elements elements_aux]. constructor.
  - cbn [elements elements_aux].
    constructor; [intro H; inversion H|constructor].
  - rewrite elements_branch, List.map_app. apply NoDup_app.
    + exact IHl.
    + exact IHr.
    + intros key Hleft Hright.
    apply in_map_iff in Hleft. destruct Hleft as [[lk lv] [Eleft Hinleft]].
    apply in_map_iff in Hright. destruct Hright as [[rk rv] [Eright Hinright]].
    cbn in Eleft, Eright. subst lk rk.
    pose proof (proj1 (all_keys_elements _ _ _) Hl key lv Hinleft) as [_ Hfalse].
    pose proof (proj1 (all_keys_elements _ _ _) Hr key rv Hinright) as [_ Htrue].
    congruence.
Qed.

Corollary wf_elements_binding_unique:
  forall (A : Type) (m : t A) key (left right : A),
    wf m -> In (key, left) (elements m) -> In (key, right) (elements m) ->
    left = right.
Proof.
  intros A m key left right Hwf Hl Hr.
  pose proof (wf_elements_complete A m Hwf key left Hl) as Hgetl.
  pose proof (wf_elements_complete A m Hwf key right Hr) as Hgetr.
  congruence.
Qed.

Lemma forallb_elements:
  forall (A : Type) (test : string -> A -> bool) (m : t A),
    forallb test m = true <->
    forall key value, In (key, value) (elements m) -> test key value = true.
Proof.
  intros A test m.
  induction m as [|key value|sample split ltree IHl rtree IHr].
  - cbn [forallb elements elements_aux].
    split; intros; [contradiction|reflexivity].
  - split.
    + cbn [forallb elements elements_aux].
      intros H k v [E|Hnone]; [now inversion E; subst|contradiction].
    + intros H. exact (H key value (or_introl eq_refl)).
  - cbn [forallb]. rewrite elements_branch, Bool.andb_true_iff, IHl, IHr.
    split.
    + intros [Hl Hr] key value Hin. apply in_app_iff in Hin.
      destruct Hin; auto.
    + intros H. split; intros key value Hin; apply H;
        apply in_or_app; auto.
Qed.

Theorem beq_correct_wf:
  forall (A : Type) (eqA : A -> A -> bool) (left right : t A),
    wf left -> wf right ->
    beq eqA left right = true <->
    forall key,
      match get key left, get key right with
      | None, None => True
      | Some left_value, Some right_value =>
          eqA left_value right_value = true
      | _, _ => False
      end.
Proof.
  intros A eqA left right Hleft Hright. unfold beq.
  rewrite Bool.andb_true_iff, !forallb_elements. split.
  - intros [Hlr Hrl] key.
    destruct (get key left) as [left_value|] eqn:Eleft;
      destruct (get key right) as [right_value|] eqn:Eright; cbn.
    + pose proof (Hlr key left_value
        (@get_elements_sound A left key left_value Eleft)) as Hvalue.
      now rewrite Eright in Hvalue.
    + specialize (Hlr key left_value
        (@get_elements_sound A left key left_value Eleft)).
      now rewrite Eright in Hlr.
    + specialize (Hrl key right_value
        (@get_elements_sound A right key right_value Eright)).
      now rewrite Eleft in Hrl.
    + exact I.
  - intros Hpoint. split.
    + intros key value Hin.
      pose proof (@wf_elements_complete A left Hleft key value Hin) as Eleft.
      specialize (Hpoint key). rewrite Eleft in Hpoint.
      destruct (get key right); cbn in Hpoint |- *;
        [exact Hpoint|contradiction].
    + intros key value Hin.
      pose proof (@wf_elements_complete A right Hright key value Hin) as Eright.
      specialize (Hpoint key). rewrite Eright in Hpoint.
      destruct (get key left); cbn in Hpoint |- *;
        [exact Hpoint|contradiction].
Qed.

Corollary beq_extensional_wf:
  forall (A : Type) (eqA : A -> A -> bool) (left right : t A),
    (forall x y, eqA x y = true <-> x = y) ->
    wf left -> wf right ->
    beq eqA left right = true <->
    forall key, get key left = get key right.
Proof.
  intros A eqA left right Heq Hleft Hright.
  rewrite (beq_correct_wf A eqA left right Hleft Hright).
  split.
  - intros Hpoint key. specialize (Hpoint key).
    destruct (get key left) as [left_value|] eqn:Eleft;
      destruct (get key right) as [right_value|] eqn:Eright; cbn in Hpoint.
    + apply (proj1 (Heq left_value right_value)) in Hpoint.
      now subst.
    + contradiction.
    + contradiction.
    + reflexivity.
  - intros Hlookup key. specialize (Hlookup key).
    destruct (get key left) as [left_value|] eqn:Eleft;
      destruct (get key right) as [right_value|] eqn:Eright;
      cbn in Hlookup |- *; try congruence; try exact I.
    apply (proj2 (Heq left_value right_value)). congruence.
Qed.

Lemma representative_all_keys:
  forall (A : Type) (P : string -> Prop) (m : t A) key,
    all_keys P m -> representative m = Some key -> P key.
Proof.
  intros A P m key Hall Hrep.
  destruct (representative_elements A m key Hrep) as [value Hin].
  exact (proj1 (all_keys_elements A P m) Hall key value Hin).
Qed.

Lemma all_splits_after_of_all_keys:
  forall (A : Type) outer_sample bound side (m : t A),
    wf m ->
    all_keys (fun key =>
      same_prefix outer_sample key bound /\ bit_at key bound = side) m ->
    splits_after bound m.
Proof.
  intros A outer_sample bound side m Hwf.
  revert outer_sample bound side.
  induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros outer_sample bound side Hall; cbn in *.
  - exact I.
  - exact I.
  - destruct Hall as [Houter_left Houter_right].
    destruct (representative ltree) as [left_key|] eqn:Eleft;
      [|exfalso; apply Hnel; reflexivity].
    destruct (representative rtree) as [right_key|] eqn:Eright;
      [|exfalso; apply Hner; reflexivity].
    assert (Houter_left_key :
      same_prefix outer_sample left_key bound /\
      bit_at left_key bound = side).
    { exact (representative_all_keys A _ ltree left_key Houter_left Eleft). }
    assert (Houter_right_key :
      same_prefix outer_sample right_key bound /\
      bit_at right_key bound = side).
    { exact (representative_all_keys A _ rtree right_key Houter_right Eright). }
    assert (Hinner_left_key :
      same_prefix sample left_key split /\ bit_at left_key split = false).
    { exact (representative_all_keys A _ ltree left_key Hl Eleft). }
    assert (Hinner_right_key :
      same_prefix sample right_key split /\ bit_at right_key split = true).
    { exact (representative_all_keys A _ rtree right_key Hr Eright). }
    assert (Hbound : bound < split).
    { destruct (Nat.lt_ge_cases bound split) as [Hlt|Hge]; [exact Hlt|].
      apply (proj1 (Nat.lt_eq_cases split bound)) in Hge.
      destruct Hge as [Hlt'|Heq].
      - assert (Hsame : bit_at left_key split = bit_at right_key split).
        { rewrite <- (proj1 Houter_left_key split Hlt').
          rewrite <- (proj1 Houter_right_key split Hlt'). reflexivity. }
        rewrite (proj2 Hinner_left_key), (proj2 Hinner_right_key) in Hsame.
        discriminate.
      - subst bound.
        assert (Hsame : bit_at left_key split = bit_at right_key split).
        { rewrite (proj2 Houter_left_key), (proj2 Houter_right_key).
          reflexivity. }
        rewrite (proj2 Hinner_left_key), (proj2 Hinner_right_key) in Hsame.
        discriminate. }
    repeat split; try assumption.
    + now apply (IHl outer_sample bound side).
    + now apply (IHr outer_sample bound side).
Qed.

Theorem wf_splits_ordered:
  forall (A : Type) (m : t A), wf m -> splits_ordered m.
Proof.
  intros A m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; cbn.
  - exact I.
  - exact I.
  - repeat split; try assumption.
    + now apply (all_splits_after_of_all_keys A sample split false ltree).
    + now apply (all_splits_after_of_all_keys A sample split true rtree).
Qed.

Lemma same_prefix_rebase:
  forall old new key split,
    same_prefix old new split -> same_prefix old key split ->
    same_prefix new key split.
Proof.
  unfold same_prefix. intros old new key split Hnew Hkey n Hn.
  rewrite <- (Hnew n Hn). apply Hkey. exact Hn.
Qed.

Lemma same_prefix_refl:
  forall sample split, same_prefix sample sample split.
Proof.
  unfold same_prefix. intros. reflexivity.
Qed.

Lemma same_prefix_shrink:
  forall left right outer inner,
    same_prefix left right outer -> inner <= outer ->
    same_prefix left right inner.
Proof.
  unfold same_prefix. intros left right outer inner Hprefix Hle n Hn.
  apply Hprefix. lia.
Qed.

(** Equal branch splits may use either resident sample.  Rebase the second
    tree's invariant onto the first sample without changing its routing
    side. *)
Lemma all_keys_equal_split_rebase:
  forall (A : Type) left_sample right_sample split side (m : t A),
    same_prefix left_sample right_sample split ->
    all_keys (fun key =>
      same_prefix right_sample key split /\ bit_at key split = side) m ->
    all_keys (fun key =>
      same_prefix left_sample key split /\ bit_at key split = side) m.
Proof.
  intros A left_sample right_sample split side m Hsamples Hall.
  eapply all_keys_impl; [exact Hall|].
  intros key [Hprefix Hbit]. split; [|exact Hbit].
  unfold same_prefix in *. intros n Hn.
  rewrite (Hsamples n Hn). now apply Hprefix.
Qed.

Lemma branch_all_prefix:
  forall (A : Type) sample split (ltree rtree : t A),
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) ltree ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) rtree ->
    all_keys (fun key => same_prefix sample key split)
      (Branch sample split ltree rtree).
Proof.
  intros A sample split ltree rtree Hleft Hright. cbn. split.
  - eapply all_keys_impl; [exact Hleft|]. intros key H. exact (proj1 H).
  - eapply all_keys_impl; [exact Hright|]. intros key H. exact (proj1 H).
Qed.

(** Below a branch's own split, all of its keys have the sample's bit.  This
    is the containment fact used when one merge root lies below the other. *)
Lemma all_keys_contained_prefix:
  forall (A : Type) outer_sample inner_sample outer_split inner_split
      (m : t A),
    same_prefix outer_sample inner_sample outer_split ->
    outer_split < inner_split ->
    all_keys (fun key => same_prefix inner_sample key inner_split) m ->
    all_keys (fun key =>
      same_prefix outer_sample key outer_split /\
      bit_at key outer_split = bit_at inner_sample outer_split) m.
Proof.
  intros A outer_sample inner_sample outer_split inner_split m
    Hsamples Hlt Hall.
  eapply all_keys_impl; [exact Hall|].
  intros key Hprefix. split.
  - unfold same_prefix in *. intros n Hn.
    rewrite (Hsamples n Hn). apply Hprefix. lia.
  - symmetry. apply Hprefix. lia.
Qed.

Lemma agrees_before_bounded_false_first_diff:
  forall left right split,
    agrees_before_bounded left right split = false ->
    exists differing,
      first_diff left right = Some differing /\ differing < split.
Proof.
  intros left right split Hdisagree.
  rewrite agrees_before_bounded_eq in Hdisagree.
  unfold agrees_before in Hdisagree.
  destruct (first_diff left right) as [differing|] eqn:Hdiff.
  - exists differing. split; [reflexivity|].
    now apply Nat.leb_gt.
  - discriminate.
Qed.

(** A failed prefix comparison before the shallower root yields one exact
    split that separates every key in the two trees.  The result is already
    in the shape consumed by [join_separated_correct_wf]. *)
Lemma branches_disjoint_prefix:
  forall (A B : Type) left_sample left_split (left : t A)
      right_sample right_split (right : t B),
    all_keys (fun key => same_prefix left_sample key left_split) left ->
    all_keys (fun key => same_prefix right_sample key right_split) right ->
    agrees_before_bounded left_sample right_sample
      (Nat.min left_split right_split) = false ->
    exists differing,
      first_diff left_sample right_sample = Some differing /\
      all_keys (fun key =>
        same_prefix left_sample key differing /\
        bit_at key differing = bit_at left_sample differing) left /\
      all_keys (fun key =>
        same_prefix left_sample key differing /\
        bit_at key differing = negb (bit_at left_sample differing)) right.
Proof.
  intros A B left_sample left_split left right_sample right_split right
    Hleft Hright Hdisagree.
  destruct (agrees_before_bounded_false_first_diff _ _ _ Hdisagree)
    as [differing [Hdiff Hlt]].
  destruct (first_diff_spec _ _ _ Hdiff) as [Hbit Hbefore].
  assert (Hlt_left : differing < left_split) by
    (eapply Nat.lt_le_trans; [exact Hlt|apply Nat.le_min_l]).
  assert (Hlt_right : differing < right_split) by
    (eapply Nat.lt_le_trans; [exact Hlt|apply Nat.le_min_r]).
  exists differing. split; [exact Hdiff|]. split.
  - eapply all_keys_contained_prefix.
    + apply same_prefix_refl.
    + exact Hlt_left.
    + exact Hleft.
  - eapply all_keys_impl; [exact Hright|].
    intros key Hprefix. split.
    + unfold same_prefix in *. intros n Hn.
      rewrite (Hbefore n Hn). apply Hprefix. lia.
    + assert (Hkey : bit_at key differing = bit_at right_sample differing).
      { symmetry. apply Hprefix. exact Hlt_right. }
      rewrite Hkey. destruct (bit_at left_sample differing),
        (bit_at right_sample differing); cbn in *; congruence.
Qed.

Lemma all_keys_branch:
  forall (A : Type) (P : string -> Prop) sample split (ltree rtree : t A),
    all_keys P ltree -> all_keys P rtree ->
    all_keys P (branch sample split ltree rtree).
Proof.
  intros A P sample split ltree rtree Hl Hr.
  unfold branch. destruct ltree; destruct rtree; cbn in *; try tauto.
  all: repeat match goal with
       | |- context [match representative ?m with _ => _ end] =>
           destruct (representative m)
       end; cbn; tauto.
Qed.

Lemma all_keys_get:
  forall (A : Type) (P : string -> Prop) (m : t A) key value,
    all_keys P m -> get key m = Some value -> P key.
Proof.
  intros A P m key value Hall Hget.
  apply (proj1 (all_keys_elements A P m) Hall key value).
  now apply get_elements_sound.
Qed.

Lemma get_none_if_all_keys:
  forall (A : Type) (P : string -> Prop) (m : t A) key,
    all_keys P m -> (P key -> False) -> get key m = None.
Proof.
  intros A P m key Hall Hcontra. destruct (get key m) eqn:E; [|reflexivity].
  exfalso. apply Hcontra. eapply all_keys_get; eauto.
Qed.

Lemma get_branch:
  forall (A : Type) sample split (ltree rtree : t A) key,
    all_keys (fun stored => bit_at stored split = false) ltree ->
    all_keys (fun stored => bit_at stored split = true) rtree ->
    get key (branch sample split ltree rtree) =
      if bit_at key split then get key rtree else get key ltree.
Proof.
  intros A sample split ltree rtree key Hl Hr.
  assert (Hleft_wrong : bit_at key split = true -> get key ltree = None).
  { intros Hbit. eapply get_none_if_all_keys; [exact Hl|].
    intros Hfalse. congruence. }
  assert (Hright_wrong : bit_at key split = false -> get key rtree = None).
  { intros Hbit. eapply get_none_if_all_keys; [exact Hr|].
    intros Htrue. congruence. }
  destruct (bit_at key split) eqn:E.
  - pose proof (Hleft_wrong eq_refl) as Hleftnone. unfold branch.
    destruct ltree; destruct rtree; cbn [get representative] in *;
      try rewrite E; try reflexivity; try congruence.
    all: repeat match goal with
         | |- context [match representative ?m with _ => _ end] =>
             destruct (representative m)
         end; cbn [get]; rewrite E; reflexivity.
  - pose proof (Hright_wrong eq_refl) as Hrightnone. unfold branch.
    destruct ltree; destruct rtree; cbn [get representative] in *;
      try rewrite E; try reflexivity; try congruence.
    all: repeat match goal with
         | |- context [match representative ?m with _ => _ end] =>
             destruct (representative m)
         end; cbn [get]; rewrite E; reflexivity.
Qed.

Lemma branch_wf:
  forall (A : Type) sample split (ltree rtree : t A),
    wf ltree -> wf rtree ->
    representative ltree <> None -> representative rtree <> None ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) ltree ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) rtree ->
    wf (branch sample split ltree rtree).
Proof.
  intros A sample split ltree rtree Hwl Hwr Hnel Hner Hl Hr.
  assert (Hleft_rebase : forall new_sample,
    representative ltree = Some new_sample ->
    all_keys (fun key =>
      same_prefix new_sample key split /\ bit_at key split = false) ltree).
  { intros new_sample Hrep. eapply all_keys_impl; [exact Hl|].
    intros key [Hprefix Hbit]. split; [|exact Hbit].
    eapply same_prefix_rebase; [|exact Hprefix].
    exact (proj1 (representative_all_keys A
      (fun stored => same_prefix sample stored split /\
                     bit_at stored split = false)
      ltree new_sample Hl Hrep)). }
  assert (Hright_rebase : forall new_sample,
    representative ltree = Some new_sample ->
    all_keys (fun key =>
      same_prefix new_sample key split /\ bit_at key split = true) rtree).
  { intros new_sample Hrep. eapply all_keys_impl; [exact Hr|].
    intros key [Hprefix Hbit]. split; [|exact Hbit].
    eapply same_prefix_rebase; [|exact Hprefix].
    exact (proj1 (representative_all_keys A
      (fun stored => same_prefix sample stored split /\
                     bit_at stored split = false)
      ltree new_sample Hl Hrep)). }
  unfold branch.
  destruct ltree as [|left_key left_value|left_sample left_split left_left left_right];
    [exfalso; apply Hnel; reflexivity| |];
  destruct rtree as [|right_key right_value|right_sample right_split right_left right_right];
    try (exfalso; apply Hner; reflexivity).
  - cbn. apply wf_branch.
    + exact Hwl.
    + exact Hwr.
    + exact Hnel.
    + exact Hner.
    + apply Hleft_rebase. reflexivity.
    + apply Hright_rebase. reflexivity.
  - cbn. apply wf_branch.
    + exact Hwl.
    + exact Hwr.
    + exact Hnel.
    + exact Hner.
    + apply Hleft_rebase. reflexivity.
    + apply Hright_rebase. reflexivity.
  - destruct (representative (Branch left_sample left_split left_left left_right))
      eqn:Erep.
    + apply wf_branch.
      * exact Hwl.
      * exact Hwr.
      * rewrite Erep. discriminate.
      * exact Hner.
      * apply Hleft_rebase. reflexivity.
      * apply Hright_rebase. reflexivity.
    + exfalso. apply Hnel. reflexivity.
  - destruct (representative (Branch left_sample left_split left_left left_right))
      eqn:Erep.
    + apply wf_branch.
      * exact Hwl.
      * exact Hwr.
      * rewrite Erep. discriminate.
      * exact Hner.
      * apply Hleft_rebase. reflexivity.
      * apply Hright_rebase. reflexivity.
    + exfalso. apply Hnel. reflexivity.
Qed.

Lemma remove_changed_some_reference:
  forall (A : Type) key (m changed : t A),
    remove_changed key m = Some changed ->
    remove_reference key m = changed.
Proof.
  intros A key m.
  induction m as [|stored value|sample split ltree IHl rtree IHr];
    intros changed Hchanged.
  - discriminate.
  - cbn [remove_changed remove_reference] in *.
    destruct (String.eqb key stored); inversion Hchanged. reflexivity.
  - cbn [remove_changed remove_reference] in *.
    destruct (bit_at key split).
    + destruct (remove_changed key rtree) as [rtree'|] eqn:E;
        inversion Hchanged; subst.
      now rewrite (IHr rtree' eq_refl).
    + destruct (remove_changed key ltree) as [ltree'|] eqn:E;
        inversion Hchanged; subst.
      now rewrite (IHl ltree' eq_refl).
Qed.

Lemma remove_changed_none_get:
  forall (A : Type) key (m : t A),
    remove_changed key m = None -> get key m = None.
Proof.
  intros A key m.
  induction m as [|stored value|sample split ltree IHl rtree IHr]; intro Hchanged.
  - reflexivity.
  - cbn [remove_changed get] in *.
    now destruct (String.eqb key stored).
  - cbn [remove_changed get] in *.
    destruct (bit_at key split).
    + destruct (remove_changed key rtree) eqn:E; [discriminate|].
      now apply IHr.
    + destruct (remove_changed key ltree) eqn:E; [discriminate|].
      now apply IHl.
Qed.

Lemma remove_changed_none_of_get_none:
  forall (A : Type) key (m : t A),
    get key m = None -> remove_changed key m = None.
Proof.
  intros A key m.
  induction m as [|stored value|sample split ltree IHl rtree IHr]; intro Hget.
  - reflexivity.
  - cbn [get remove_changed] in *.
    now destruct (String.eqb key stored).
  - cbn [get remove_changed] in *.
    destruct (bit_at key split); [now rewrite IHr|now rewrite IHl].
Qed.

Theorem remove_absent_identity:
  forall (A : Type) key (m : t A),
    get key m = None -> remove key m = m.
Proof.
  intros A key m Hget. unfold remove.
  now rewrite (@remove_changed_none_of_get_none A key m Hget).
Qed.

Lemma all_keys_remove_reference:
  forall (A : Type) (P : string -> Prop) (m : t A) key,
    all_keys P m -> all_keys P (remove_reference key m).
Proof.
  intros A P m. induction m as [|stored value|sample split ltree IHl rtree IHr];
    intros key Hall; cbn [remove_reference] in *.
  - exact I.
  - destruct (String.eqb key stored); cbn; [exact I|exact Hall].
  - destruct Hall as [Hl Hr]. destruct (bit_at key split).
    + apply all_keys_branch; [exact Hl|now apply IHr].
    + apply all_keys_branch; [now apply IHl|exact Hr].
Qed.

Lemma all_keys_remove:
  forall (A : Type) (P : string -> Prop) (m : t A) key,
    all_keys P m -> all_keys P (remove key m).
Proof.
  intros A P m key Hall. unfold remove.
  destruct (remove_changed key m) as [changed|] eqn:E; [|exact Hall].
  rewrite <- (@remove_changed_some_reference A key m changed E).
  now apply all_keys_remove_reference.
Qed.

Lemma wf_representative_none:
  forall (A : Type) (m : t A),
    wf m -> representative m = None -> m = Empty.
Proof.
  intros A m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros Hrep; cbn in Hrep.
  - reflexivity.
  - discriminate.
  - destruct (representative ltree) eqn:Eleft.
    + discriminate.
    + exfalso. now apply Hnel.
Qed.

Lemma branch_wf_general:
  forall (A : Type) sample split (ltree rtree : t A),
    wf ltree -> wf rtree ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = false) ltree ->
    all_keys (fun key =>
      same_prefix sample key split /\ bit_at key split = true) rtree ->
    wf (branch sample split ltree rtree).
Proof.
  intros A sample split ltree rtree Hwl Hwr Hl Hr.
  destruct (representative ltree) eqn:Eleft.
  - destruct (representative rtree) eqn:Eright.
    + apply branch_wf; try assumption; congruence.
    + pose proof (wf_representative_none A rtree Hwr Eright) as ->.
      unfold branch. destruct ltree; exact Hwl.
  - pose proof (wf_representative_none A ltree Hwl Eleft) as ->.
    unfold branch. exact Hwr.
Qed.

Theorem remove_reference_wf:
  forall (A : Type) key (m : t A), wf m -> wf (remove_reference key m).
Proof.
  intros A key m Hwf. induction Hwf as
      [|stored value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; cbn [remove_reference].
  - constructor.
  - destruct (String.eqb key stored); constructor.
  - destruct (bit_at key split).
    + apply branch_wf_general.
      * exact Hwl.
      * exact IHr.
      * exact Hl.
      * now apply all_keys_remove_reference.
    + apply branch_wf_general.
      * exact IHl.
      * exact Hwr.
      * now apply all_keys_remove_reference.
      * exact Hr.
Qed.

Theorem remove_wf:
  forall (A : Type) key (m : t A), wf m -> wf (remove key m).
Proof.
  intros A key m Hwf. unfold remove.
  destruct (remove_changed key m) as [changed|] eqn:E; [|exact Hwf].
  rewrite <- (@remove_changed_some_reference A key m changed E).
  now apply remove_reference_wf.
Qed.

Theorem get_remove_reference:
  forall (A : Type) key query (m : t A),
    wf m ->
    get query (remove_reference key m) =
      if String.eqb query key then None else get query m.
Proof.
  intros A key query m Hwf. induction Hwf as
      [|stored value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr].
  - cbn. destruct (String.eqb query key); reflexivity.
  - cbn [remove_reference get]. destruct (String.string_dec query key) as [->|Hqk].
    + rewrite String.eqb_refl. destruct (String.eqb key stored) eqn:Eks;
        cbn [get]; rewrite ?Eks; reflexivity.
    + assert (Eqk : String.eqb query key = false) by
        (apply String.eqb_neq; exact Hqk).
      rewrite Eqk. destruct (String.eqb key stored) eqn:Eks.
      * apply String.eqb_eq in Eks. subst stored.
        assert (Eqs : String.eqb query key = false) by
          (apply String.eqb_neq; exact Hqk).
        now rewrite Eqs.
      * reflexivity.
  - cbn [remove_reference].
    assert (Hlbit : all_keys (fun stored => bit_at stored split = false) ltree).
    { eapply all_keys_impl; [exact Hl|]. intros stored H. exact (proj2 H). }
    assert (Hrbit : all_keys (fun stored => bit_at stored split = true) rtree).
    { eapply all_keys_impl; [exact Hr|]. intros stored H. exact (proj2 H). }
    destruct (bit_at key split) eqn:Ekey.
    + rewrite (get_branch A sample split ltree (remove_reference key rtree) query).
      * destruct (bit_at query split) eqn:Equery.
        -- rewrite IHr. cbn [get]. now rewrite Equery.
        -- assert (Hneq : query <> key).
           { intros ->. rewrite Ekey in Equery. discriminate. }
           assert (Eneq : String.eqb query key = false) by
             (apply String.eqb_neq; exact Hneq).
           cbn [get]. now rewrite Equery, Eneq.
      * exact Hlbit.
      * now apply all_keys_remove_reference.
    + rewrite (get_branch A sample split (remove_reference key ltree) rtree query).
      * destruct (bit_at query split) eqn:Equery.
        -- assert (Hneq : query <> key).
           { intros ->. rewrite Ekey in Equery. discriminate. }
           assert (Eneq : String.eqb query key = false) by
             (apply String.eqb_neq; exact Hneq).
           cbn [get]. now rewrite Equery, Eneq.
        -- rewrite IHl. cbn [get]. now rewrite Equery.
      * now apply all_keys_remove_reference.
      * exact Hrbit.
Qed.

Theorem get_remove:
  forall (A : Type) key query (m : t A),
    wf m ->
    get query (remove key m) =
      if String.eqb query key then None else get query m.
Proof.
  intros A key query m Hwf. unfold remove.
  destruct (remove_changed key m) as [changed|] eqn:E.
  - rewrite <- (@remove_changed_some_reference A key m changed E).
    now apply get_remove_reference.
  - pose proof (@remove_changed_none_get A key m E) as Hnone.
    destruct (String.eqb query key) eqn:Equery; [|reflexivity].
    apply String.eqb_eq in Equery. now subst query.
Qed.

Corollary get_remove_same:
  forall (A : Type) key (m : t A),
    wf m -> get key (remove key m) = None.
Proof.
  intros. rewrite get_remove by exact H. now rewrite String.eqb_refl.
Qed.

Corollary get_remove_other:
  forall (A : Type) key query (m : t A),
    wf m -> query <> key ->
    get query (remove key m) = get query m.
Proof.
  intros. rewrite get_remove by exact H.
  apply String.eqb_neq in H0. now rewrite H0.
Qed.

Theorem elements_remove_spec:
  forall (A : Type) key (m : t A),
    wf m -> forall stored value,
    In (stored, value) (elements (remove key m)) <->
      stored <> key /\ In (stored, value) (elements m).
Proof.
  intros A key m Hwf stored value. split.
  - intros Hin.
    assert (Hneq : stored <> key).
    { intros ->.
      pose proof (wf_elements_complete A (remove key m)
        (remove_wf A key m Hwf) key value Hin) as Hget.
      rewrite get_remove_same in Hget by exact Hwf. discriminate. }
    split; [exact Hneq|]. apply get_elements_sound.
    pose proof (wf_elements_complete A (remove key m)
      (remove_wf A key m Hwf) stored value Hin) as Hget.
    rewrite (get_remove_other A key stored m Hwf Hneq) in Hget. exact Hget.
  - intros [Hneq Hin].
    apply get_elements_sound. rewrite (get_remove_other A key stored m Hwf Hneq).
    now apply (wf_elements_complete A m Hwf).
Qed.

Lemma representative_map:
  forall (A B : Type) (f : string -> A -> B) (m : t A),
    representative (map f m) = representative m.
Proof.
  intros A B f m. induction m as [|key value|sample split ltree IHl rtree IHr];
    cbn; [reflexivity|reflexivity|].
  now rewrite IHl, IHr.
Qed.

Lemma all_keys_map:
  forall (A B : Type) (P : string -> Prop) (f : string -> A -> B) (m : t A),
    all_keys P (map f m) <-> all_keys P m.
Proof.
  intros A B P f m. induction m as [|key value|sample split ltree IHl rtree IHr];
    cbn; [tauto|tauto|]. now rewrite IHl, IHr.
Qed.

Theorem map_wf:
  forall (A B : Type) (f : string -> A -> B) (m : t A),
    wf m -> wf (map f m).
Proof.
  intros A B f m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; cbn [map].
  - constructor.
  - constructor.
  - apply wf_branch.
    + exact IHl.
    + exact IHr.
    + rewrite representative_map. exact Hnel.
    + rewrite representative_map. exact Hner.
    + apply (proj2 (all_keys_map A B _ f ltree)). exact Hl.
    + apply (proj2 (all_keys_map A B _ f rtree)). exact Hr.
Qed.

(** Filtering is the first missing merge dependency.  Unlike [map], it may
    remove every binding below a branch, so its invariant proof deliberately
    goes through the collapsing smart [branch] constructor. *)
Lemma all_keys_map_filter:
  forall (A B : Type) (P : string -> Prop)
      (f : string -> A -> option B) (m : t A),
    all_keys P m -> all_keys P (map_filter f m).
Proof.
  intros A B P f m. induction m as
      [|key value|sample split ltree IHl rtree IHr]; intros Hall;
    cbn [map_filter] in *.
  - exact I.
  - destruct (f key value); cbn; [exact Hall|exact I].
  - destruct Hall as [Hl Hr]. apply all_keys_branch.
    + now apply IHl.
    + now apply IHr.
Qed.

Theorem map_filter_wf:
  forall (A B : Type) (f : string -> A -> option B) (m : t A),
    wf m -> wf (map_filter f m).
Proof.
  intros A B f m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; cbn [map_filter].
  - constructor.
  - destruct (f key value); constructor.
  - apply branch_wf_general.
    + exact IHl.
    + exact IHr.
    + now apply all_keys_map_filter.
    + now apply all_keys_map_filter.
Qed.

Theorem get_map_filter_wf:
  forall (A B : Type) (f : string -> A -> option B) (m : t A),
    wf m -> forall query,
    get query (map_filter f m) =
      match get query m with None => None | Some value => f query value end.
Proof.
  intros A B f m Hwf. induction Hwf as
      [|key value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros query.
  - reflexivity.
  - cbn [map_filter get]. destruct (f key value) as [result|] eqn:Eresult;
      destruct (String.eqb query key) eqn:Equery; cbn.
    + apply String.eqb_eq in Equery. subst query.
      now rewrite String.eqb_refl, Eresult.
    + now rewrite Equery.
    + apply String.eqb_eq in Equery. subst query.
      now rewrite Eresult.
    + reflexivity.
  - assert (Hlbit : all_keys (fun stored => bit_at stored split = false) ltree).
    { eapply all_keys_impl; [exact Hl|]. intros stored H. exact (proj2 H). }
    assert (Hrbit : all_keys (fun stored => bit_at stored split = true) rtree).
    { eapply all_keys_impl; [exact Hr|]. intros stored H. exact (proj2 H). }
    assert (Hlfiltered : all_keys
      (fun stored => bit_at stored split = false) (map_filter f ltree)).
    { now apply all_keys_map_filter. }
    assert (Hrfiltered : all_keys
      (fun stored => bit_at stored split = true) (map_filter f rtree)).
    { now apply all_keys_map_filter. }
    cbn [map_filter]. rewrite (get_branch B sample split
      (map_filter f ltree) (map_filter f rtree) query Hlfiltered Hrfiltered).
    cbn [get]. destruct (bit_at query split); [apply IHr|apply IHl].
Qed.

Theorem map_left_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C) (m : t A),
    f None None = None -> wf m -> wf (map_left f m) /\
    forall key, get key (map_left f m) = f (get key m) None.
Proof.
  intros A B C f m Hnone Hwf. unfold map_left. split.
  - now apply map_filter_wf.
  - intro key. rewrite get_map_filter_wf by exact Hwf.
    destruct (get key m); [reflexivity|symmetry; exact Hnone].
Qed.

Theorem map_right_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C) (m : t B),
    f None None = None -> wf m -> wf (map_right f m) /\
    forall key, get key (map_right f m) = f None (get key m).
Proof.
  intros A B C f m Hnone Hwf. unfold map_right. split.
  - now apply map_filter_wf.
  - intro key. rewrite get_map_filter_wf by exact Hwf.
    destruct (get key m); [reflexivity|symmetry; exact Hnone].
Qed.

Lemma get_routed_key_self:
  forall (A : Type) key value (m : t A),
    get key m = Some value -> routed_key key m = Some key.
Proof.
  intros A key value m. induction m as
      [|stored stored_value|sample split ltree IHl rtree IHr];
    intros Hget; cbn in *.
  - discriminate.
  - destruct (String.eqb key stored) eqn:E; [|discriminate].
    apply String.eqb_eq in E. now subst.
  - destruct (bit_at key split); eauto.
Qed.

Lemma representative_replace_same:
  forall (A : Type) key value (m : t A),
    routed_key key m = Some key ->
    representative (replace key value m) = representative m.
Proof.
  intros A key value m. induction m as
      [|stored stored_value|sample split ltree IHl rtree IHr];
    intros Hrouted.
  - discriminate.
  - cbn in Hrouted. inversion Hrouted. reflexivity.
  - destruct (bit_at key split) eqn:E.
    + cbn [routed_key] in Hrouted. rewrite E in Hrouted.
      cbn [replace representative]. rewrite E.
      destruct (representative ltree) eqn:Eleft.
      * cbn [representative]. now rewrite Eleft.
      * cbn [representative]. rewrite Eleft. now rewrite (IHr Hrouted).
    + cbn [routed_key] in Hrouted. rewrite E in Hrouted.
      cbn [replace representative]. rewrite E.
      cbn [representative]. now rewrite (IHl Hrouted).
Qed.

Lemma all_keys_replace_same:
  forall (A : Type) (P : string -> Prop) key value (m : t A),
    routed_key key m = Some key -> all_keys P m ->
    all_keys P (replace key value m).
Proof.
  intros A P key value m. induction m as
      [|stored stored_value|sample split ltree IHl rtree IHr];
    intros Hrouted Hall; cbn in *.
  - discriminate.
  - inversion Hrouted; subst. exact Hall.
  - destruct Hall as [Hl Hr]. destruct (bit_at key split).
    + split; [exact Hl|now apply IHr].
    + split; [now apply IHl|exact Hr].
Qed.

Theorem replace_same_correct_wf:
  forall (A : Type) key value (m : t A),
    wf m -> routed_key key m = Some key ->
    wf (replace key value m) /\
    forall query,
      get query (replace key value m) =
        if String.eqb query key then Some value else get query m.
Proof.
  intros A key value m Hwf. induction Hwf as
      [|stored stored_value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros Hrouted.
  - discriminate.
  - cbn in Hrouted. inversion Hrouted; subst stored. split; [constructor|].
    intros query. cbn [replace get]. destruct (String.eqb query key); reflexivity.
  - cbn [routed_key] in Hrouted. destruct (bit_at key split) eqn:Ekey.
    + specialize (IHr Hrouted). destruct IHr as [Hwreplace Hgetreplace]. split.
      * cbn [replace]. rewrite Ekey. apply wf_branch; try assumption.
        -- rewrite representative_replace_same by exact Hrouted. exact Hner.
        -- apply all_keys_replace_same with (key := key); assumption.
      * intros query. cbn [replace]. rewrite Ekey.
        destruct (bit_at query split) eqn:Equery.
        -- cbn [get]. rewrite Equery. apply Hgetreplace.
        -- assert (Hneq : query <> key).
           { intros ->. rewrite Ekey in Equery. discriminate. }
           apply String.eqb_neq in Hneq. cbn [get]. now rewrite Equery, Hneq.
    + specialize (IHl Hrouted). destruct IHl as [Hwreplace Hgetreplace]. split.
      * cbn [replace]. rewrite Ekey. apply wf_branch; try assumption.
        -- rewrite representative_replace_same by exact Hrouted. exact Hnel.
        -- apply all_keys_replace_same with (key := key); assumption.
      * intros query. cbn [replace]. rewrite Ekey.
        destruct (bit_at query split) eqn:Equery.
        -- assert (Hneq : query <> key).
           { intros ->. rewrite Ekey in Equery. discriminate. }
           apply String.eqb_neq in Hneq. cbn [get]. now rewrite Equery, Hneq.
        -- cbn [get]. rewrite Equery. apply Hgetreplace.
Qed.

Theorem set_existing_correct_wf:
  forall (A : Type) key old_value value (m : t A),
    wf m -> get key m = Some old_value ->
    wf (set key value m) /\
    forall query,
      get query (set key value m) =
        if String.eqb query key then Some value else get query m.
Proof.
  intros A key old_value value m Hwf Hget.
  pose proof (get_routed_key_self A key old_value m Hget) as Hrouted.
  unfold set. rewrite Hrouted, first_diff_same.
  now apply replace_same_correct_wf.
Qed.

Corollary get_set_existing_same:
  forall (A : Type) key old_value value (m : t A),
    wf m -> get key m = Some old_value ->
    get key (set key value m) = Some value.
Proof.
  intros. destruct (set_existing_correct_wf A key old_value value m H H0) as [_ Hget].
  rewrite Hget. now rewrite String.eqb_refl.
Qed.

Corollary get_set_existing_other:
  forall (A : Type) key query old_value value (m : t A),
    wf m -> get key m = Some old_value -> query <> key ->
    get query (set key value m) = get query m.
Proof.
  intros. destruct (set_existing_correct_wf A key old_value value m H H0) as [_ Hget].
  rewrite Hget. apply String.eqb_neq in H1. now rewrite H1.
Qed.

(** Fresh insertion puts a singleton on the opposite side of every existing
    binding at the first differing bit.  These small lemmas package the
    routing and invariant consequences of that construction. *)
Lemma bool_neq_negb:
  forall left right : bool, left <> right -> right = negb left.
Proof.
  intros [] []; cbn; intros H; try reflexivity; congruence.
Qed.

Lemma branch_at_leaf_wf:
  forall (A : Type) key value split (old : t A),
    wf old -> representative old <> None ->
    all_keys (fun stored =>
      same_prefix key stored split /\
      bit_at stored split = negb (bit_at key split)) old ->
    wf (branch_at key split (Leaf key value) old).
Proof.
  intros A key value split old Hwf Hnonempty Hall.
  unfold branch_at. destruct (bit_at key split) eqn:Ekey.
  - apply wf_branch.
    + exact Hwf.
    + constructor.
    + exact Hnonempty.
    + discriminate.
    + eapply all_keys_impl; [exact Hall|].
      intros stored [Hprefix Hbit]. split; [exact Hprefix|].
      exact Hbit.
    + cbn. split.
      * unfold same_prefix. intros n Hn. reflexivity.
      * exact Ekey.
  - apply wf_branch.
    + constructor.
    + exact Hwf.
    + discriminate.
    + exact Hnonempty.
    + cbn. split.
      * unfold same_prefix. intros n Hn. reflexivity.
      * exact Ekey.
    + eapply all_keys_impl; [exact Hall|].
      intros stored [Hprefix Hbit]. split; [exact Hprefix|].
      exact Hbit.
Qed.

Lemma get_branch_at_leaf:
  forall (A : Type) key value split (old : t A) query,
    all_keys (fun stored =>
      bit_at stored split = negb (bit_at key split)) old ->
    get query (branch_at key split (Leaf key value) old) =
      if String.eqb query key then Some value else get query old.
Proof.
  intros A key value split old query Hall.
  unfold branch_at. destruct (bit_at key split) eqn:Ekey;
    destruct (bit_at query split) eqn:Equery; cbn [get]; rewrite Equery.
  - destruct (String.eqb query key) eqn:Eequal.
    + reflexivity.
    + assert (Hnone : get query old = None).
      { apply (get_none_if_all_keys A
          (fun stored => bit_at stored split = false) old query).
        - exact Hall.
        - intros Hbit. rewrite Equery in Hbit. discriminate. }
      now rewrite Hnone.
  - assert (Hneq : query <> key).
    { intros ->. rewrite Ekey in Equery. discriminate. }
    apply String.eqb_neq in Hneq. now rewrite Hneq.
  - assert (Hneq : query <> key).
    { intros ->. rewrite Ekey in Equery. discriminate. }
    apply String.eqb_neq in Hneq. now rewrite Hneq.
  - destruct (String.eqb query key) eqn:Eequal.
    + reflexivity.
    + assert (Hnone : get query old = None).
      { apply (get_none_if_all_keys A
          (fun stored => bit_at stored split = true) old query).
        - exact Hall.
        - intros Hbit. rewrite Equery in Hbit. discriminate. }
      now rewrite Hnone.
Qed.

Lemma all_keys_insert_at:
  forall (A : Type) (P : string -> Prop) key value differing (m : t A),
    P key -> all_keys P m -> all_keys P (insert_at key value differing m).
Proof.
  intros A P key value differing m Hkey Hall.
  induction m as [|stored stored_value|sample split ltree IHl rtree IHr];
    cbn [insert_at] in *.
  - exact Hkey.
  - unfold branch_at. destruct (bit_at key differing); cbn; tauto.
  - destruct (Nat.ltb differing split) eqn:Ebefore.
    + destruct Hall as [Hl Hr]. unfold branch_at.
      destruct (bit_at key differing); cbn; tauto.
    + destruct Hall as [Hl Hr]. destruct (bit_at key split).
      * split; [exact Hl|now apply IHr].
      * split; [now apply IHl|exact Hr].
Qed.

Lemma wf_representative_nonempty_routed:
  forall (A : Type) (m : t A) probe routed,
    wf m -> routed_key probe m = Some routed -> representative m <> None.
Proof.
  intros A m probe routed Hwf Hrouted Hnone.
  apply wf_representative_none in Hnone; [|exact Hwf]. subst m.
  discriminate.
Qed.

Lemma wf_representative_nonempty_get:
  forall (A : Type) (m : t A) key value,
    wf m -> get key m = Some value -> representative m <> None.
Proof.
  intros A m key value Hwf Hget Hnone.
  apply wf_representative_none in Hnone; [|exact Hwf]. subst m.
  discriminate.
Qed.

Theorem insert_at_correct_wf:
  forall (A : Type) key value differing (m : t A) routed,
    wf m -> routed_key key m = Some routed ->
    first_diff key routed = Some differing ->
    wf (insert_at key value differing m) /\
    forall query,
      get query (insert_at key value differing m) =
        if String.eqb query key then Some value else get query m.
Proof.
  intros A key value differing m routed Hwf.
  induction Hwf as
      [|stored stored_value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros Hrouted Hdiff.
  - discriminate.
  - cbn in Hrouted. inversion Hrouted; subst routed.
    destruct (first_diff_spec _ _ _ Hdiff) as [Hbits Hbefore].
    assert (Hall : all_keys (fun current =>
      same_prefix key current differing /\
      bit_at current differing = negb (bit_at key differing))
      (Leaf stored stored_value)).
    { cbn. split.
      - unfold same_prefix. intros n Hn. now apply Hbefore.
      - now apply bool_neq_negb. }
    split.
    + apply branch_at_leaf_wf; [constructor|discriminate|exact Hall].
    + intro query. apply get_branch_at_leaf.
      eapply all_keys_impl; [exact Hall|]. intros current H. exact (proj2 H).
  - cbn [routed_key] in Hrouted.
    assert (Hallprefix : all_keys (fun current => same_prefix sample current split)
      (Branch sample split ltree rtree)).
    { cbn. split.
      - eapply all_keys_impl; [exact Hl|].
        intros current H. exact (proj1 H).
      - eapply all_keys_impl; [exact Hr|].
        intros current H. exact (proj1 H). }
    assert (Hrouted_full : routed_key key (Branch sample split ltree rtree) =
      Some routed).
    { cbn. destruct (bit_at key split) eqn:E; [exact Hrouted|exact Hrouted]. }
    destruct (routed_key_elements A (Branch sample split ltree rtree)
      key routed Hrouted_full) as [routed_value Hrouted_in].
    assert (Hrouted_prefix : same_prefix sample routed split).
    { apply (proj1 (all_keys_elements A (fun current => same_prefix sample current split)
      (Branch sample split ltree rtree)) Hallprefix routed routed_value
      Hrouted_in). }
    destruct (first_diff_spec _ _ _ Hdiff) as [Hbits Hbefore].
    destruct (bit_at key split) eqn:Ekey.
    + cbn [routed_key] in Hrouted.
      destruct (Nat.ltb differing split) eqn:Ebefore.
      * assert (Hbefore_split : differing < split) by
          (apply Nat.ltb_lt; exact Ebefore).
        assert (Hall : all_keys (fun current =>
          same_prefix key current differing /\
          bit_at current differing = negb (bit_at key differing))
          (Branch sample split ltree rtree)).
        { eapply all_keys_impl; [exact Hallprefix|]. intros current Hcurrent.
          split.
          - unfold same_prefix. intros n Hn.
            rewrite (Hbefore n Hn).
            rewrite <- (Hrouted_prefix n ltac:(lia)).
            exact (Hcurrent n ltac:(lia)).
          - rewrite <- (Hcurrent differing ltac:(lia)).
            rewrite (Hrouted_prefix differing ltac:(lia)).
            now apply bool_neq_negb. }
        split.
        -- cbn [insert_at]. rewrite Ebefore.
           apply branch_at_leaf_wf; [apply wf_branch; assumption| |exact Hall].
           apply (wf_representative_nonempty_routed A
             (Branch sample split ltree rtree) key routed).
           ++ apply wf_branch; assumption.
           ++ exact Hrouted_full.
        -- intro query. cbn [insert_at]. rewrite Ebefore. apply get_branch_at_leaf.
           eapply all_keys_impl; [exact Hall|]. intros current H. exact (proj2 H).
      * assert (Hrouted_bit : bit_at routed split = true).
        { destruct (routed_key_elements A rtree key routed Hrouted)
            as [right_value Hrouted_in_right].
          exact (proj2 (proj1 (all_keys_elements A _ rtree) Hr
            routed right_value Hrouted_in_right)). }
        assert (Hsplit : split < differing).
        { apply Nat.ltb_ge in Ebefore. assert (split <> differing).
          { intro E. subst differing. rewrite Ekey, Hrouted_bit in Hbits.
            congruence. }
          lia. }
        assert (Hkey_prefix : same_prefix sample key split).
        { unfold same_prefix. intros n Hn.
          rewrite (Hbefore n ltac:(lia)). exact (Hrouted_prefix n Hn). }
        assert (Hkey_right :
          same_prefix sample key split /\ bit_at key split = true).
        { split; assumption. }
        specialize (IHr Hrouted Hdiff).
        destruct IHr as [Hwinsert Hgetinsert].
        split.
        -- cbn [insert_at]. rewrite Ebefore, Ekey. apply wf_branch.
           ++ exact Hwl.
           ++ exact Hwinsert.
           ++ exact Hnel.
           ++ apply (wf_representative_nonempty_get A
                (insert_at key value differing rtree) key value Hwinsert).
              rewrite Hgetinsert. now rewrite String.eqb_refl.
           ++ exact Hl.
           ++ apply all_keys_insert_at; assumption.
        -- intro query. cbn [insert_at]. rewrite Ebefore, Ekey.
           destruct (bit_at query split) eqn:Equery.
           ++ cbn [get]. rewrite Equery. exact (Hgetinsert query).
           ++ assert (Hneq : query <> key).
              { intros ->. rewrite Ekey in Equery. discriminate. }
              apply String.eqb_neq in Hneq. cbn [get]. now rewrite Equery, Hneq.
    + cbn [routed_key] in Hrouted.
      destruct (Nat.ltb differing split) eqn:Ebefore.
      * assert (Hbefore_split : differing < split) by
          (apply Nat.ltb_lt; exact Ebefore).
        assert (Hall : all_keys (fun current =>
          same_prefix key current differing /\
          bit_at current differing = negb (bit_at key differing))
          (Branch sample split ltree rtree)).
        { eapply all_keys_impl; [exact Hallprefix|]. intros current Hcurrent.
          split.
          - unfold same_prefix. intros n Hn.
            rewrite (Hbefore n Hn).
            rewrite <- (Hrouted_prefix n ltac:(lia)).
            exact (Hcurrent n ltac:(lia)).
          - rewrite <- (Hcurrent differing ltac:(lia)).
            rewrite (Hrouted_prefix differing ltac:(lia)).
            now apply bool_neq_negb. }
        split.
        -- cbn [insert_at]. rewrite Ebefore.
           apply branch_at_leaf_wf; [apply wf_branch; assumption| |exact Hall].
           apply (wf_representative_nonempty_routed A
             (Branch sample split ltree rtree) key routed).
           ++ apply wf_branch; assumption.
           ++ exact Hrouted_full.
        -- intro query. cbn [insert_at]. rewrite Ebefore. apply get_branch_at_leaf.
           eapply all_keys_impl; [exact Hall|]. intros current H. exact (proj2 H).
      * assert (Hrouted_bit : bit_at routed split = false).
        { destruct (routed_key_elements A ltree key routed Hrouted)
            as [left_value Hrouted_in_left].
          exact (proj2 (proj1 (all_keys_elements A _ ltree) Hl
            routed left_value Hrouted_in_left)). }
        assert (Hsplit : split < differing).
        { apply Nat.ltb_ge in Ebefore. assert (split <> differing).
          { intro E. subst differing. rewrite Ekey, Hrouted_bit in Hbits.
            congruence. }
          lia. }
        assert (Hkey_prefix : same_prefix sample key split).
        { unfold same_prefix. intros n Hn.
          rewrite (Hbefore n ltac:(lia)). exact (Hrouted_prefix n Hn). }
        assert (Hkey_left :
          same_prefix sample key split /\ bit_at key split = false).
        { split; assumption. }
        specialize (IHl Hrouted Hdiff).
        destruct IHl as [Hwinsert Hgetinsert].
        split.
        -- cbn [insert_at]. rewrite Ebefore, Ekey. apply wf_branch.
           ++ exact Hwinsert.
           ++ exact Hwr.
           ++ apply (wf_representative_nonempty_get A
                (insert_at key value differing ltree) key value Hwinsert).
              rewrite Hgetinsert. now rewrite String.eqb_refl.
           ++ exact Hner.
           ++ apply all_keys_insert_at; assumption.
           ++ exact Hr.
        -- intro query. cbn [insert_at]. rewrite Ebefore, Ekey.
           destruct (bit_at query split) eqn:Equery.
           ++ assert (Hneq : query <> key).
              { intros ->. rewrite Ekey in Equery. discriminate. }
              apply String.eqb_neq in Hneq. cbn [get]. now rewrite Equery, Hneq.
           ++ cbn [get]. rewrite Equery. exact (Hgetinsert query).
Qed.

Lemma wf_routed_key_none:
  forall (A : Type) (m : t A) probe,
    wf m -> routed_key probe m = None -> m = Empty.
Proof.
  intros A m probe Hwf. induction Hwf as
      [|stored stored_value|sample split ltree rtree Hwl IHl Hwr IHr
       Hnel Hner Hl Hr]; intros Hrouted.
  - reflexivity.
  - discriminate.
  - cbn [routed_key] in Hrouted. destruct (bit_at probe split).
    + pose proof (IHr Hrouted) as Er. subst rtree.
      exfalso. apply Hner. reflexivity.
    + pose proof (IHl Hrouted) as El. subst ltree.
      exfalso. apply Hnel. reflexivity.
Qed.

Theorem set_correct_wf:
  forall (A : Type) key value (m : t A),
    wf m -> wf (set key value m) /\
    forall query,
      get query (set key value m) =
        if String.eqb query key then Some value else get query m.
Proof.
  intros A key value m Hwf. unfold set.
  destruct (routed_key key m) as [routed|] eqn:Hrouted.
  - destruct (first_diff key routed) as [differing|] eqn:Hdiff.
    + now apply (insert_at_correct_wf A key value differing m routed).
    + apply first_diff_none_iff in Hdiff. subst routed.
      now apply (replace_same_correct_wf A key value m).
  - pose proof (wf_routed_key_none A m key Hwf Hrouted) as ->.
    split; [constructor|]. intros query.
    cbn [get]. destruct (String.eqb query key); reflexivity.
Qed.

Corollary get_set_same:
  forall (A : Type) key value (m : t A),
    wf m -> get key (set key value m) = Some value.
Proof.
  intros A key value m Hwf.
  destruct (set_correct_wf A key value m Hwf) as [_ Hget].
  rewrite Hget. now rewrite String.eqb_refl.
Qed.

Corollary get_set_other:
  forall (A : Type) key query value (m : t A),
    wf m -> query <> key -> get query (set key value m) = get query m.
Proof.
  intros A key query value m Hwf Hneq.
  destruct (set_correct_wf A key value m Hwf) as [_ Hget].
  rewrite Hget. apply String.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Theorem replace_binding_correct_wf:
  forall (A : Type) key (value : option A) (m : t A),
    wf m -> wf (replace_binding key value m) /\
    forall query,
      get query (replace_binding key value m) =
        match value with
        | Some result =>
            if String.eqb query key then Some result else get query m
        | None =>
            if String.eqb query key then None else get query m
        end.
Proof.
  intros A key [result|] m Hwf; cbn [replace_binding].
  - now apply (set_correct_wf A key result m).
  - split; [now apply remove_wf|].
    intro query. now apply (get_remove A key query m).
Qed.

Theorem combine_leaf_left_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      key value (m : t B),
    f None None = None -> wf m ->
    wf (combine_leaf_left f key value m) /\
    forall query,
      get query (combine_leaf_left f key value m) =
        f (if String.eqb query key then Some value else None) (get query m).
Proof.
  intros A B C f key value m Hnone Hwf.
  unfold combine_leaf_left. destruct (get key m) as [old|] eqn:Ekey.
  - split.
    + now apply map_filter_wf.
    + intro query. rewrite get_map_filter_wf by exact Hwf.
      destruct (get query m) as [found|] eqn:Equery; cbn.
      * now destruct (String.eqb query key).
      * destruct (String.eqb query key) eqn:Eequal.
        -- apply String.eqb_eq in Eequal. subst query. congruence.
        -- symmetry. exact Hnone.
  - destruct (@map_right_correct_wf A B C f m Hnone Hwf)
      as [Hwmap Hgetmap].
    destruct (replace_binding_correct_wf C key (f (Some value) None)
      (map_right f m) Hwmap) as [Hwreplace Hgetreplace].
    split; [exact Hwreplace|]. intro query.
    rewrite Hgetreplace, Hgetmap.
    destruct (String.eqb query key) eqn:Eequal.
    + apply String.eqb_eq in Eequal. subst query. rewrite Ekey.
      now destruct (f (Some value) None).
    + now destruct (f (Some value) None).
Qed.

Theorem combine_leaf_right_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (m : t A) key value,
    f None None = None -> wf m ->
    wf (combine_leaf_right f m key value) /\
    forall query,
      get query (combine_leaf_right f m key value) =
        f (get query m) (if String.eqb query key then Some value else None).
Proof.
  intros A B C f m key value Hnone Hwf.
  unfold combine_leaf_right. destruct (get key m) as [old|] eqn:Ekey.
  - split.
    + now apply map_filter_wf.
    + intro query. rewrite get_map_filter_wf by exact Hwf.
      destruct (get query m) as [found|] eqn:Equery; cbn.
      * now destruct (String.eqb query key).
      * destruct (String.eqb query key) eqn:Eequal.
        -- apply String.eqb_eq in Eequal. subst query. congruence.
        -- symmetry. exact Hnone.
  - destruct (@map_left_correct_wf A B C f m Hnone Hwf)
      as [Hwmap Hgetmap].
    destruct (replace_binding_correct_wf C key (f None (Some value))
      (map_left f m) Hwmap) as [Hwreplace Hgetreplace].
    split; [exact Hwreplace|]. intro query.
    rewrite Hgetreplace, Hgetmap.
    destruct (String.eqb query key) eqn:Eequal.
    + apply String.eqb_eq in Eequal. subst query. rewrite Ekey.
      now destruct (f None (Some value)).
    + now destruct (f None (Some value)).
Qed.

(** The generic merge explores at most one of six smaller branch-pair shapes
    at each branch/branch step.  This conservative predicate is independent
    of the string-prefix tests, which makes the public size bound reusable by
    the semantic merge proof. *)
Fixpoint combine_fuel_sufficient {A B : Type}
    (fuel : nat) (left : t A) (right : t B) : Prop :=
  match fuel with
  | O => False
  | S fuel' =>
      match left, right with
      | Branch _ _ left_left left_right, Branch _ _ right_left right_right =>
          combine_fuel_sufficient fuel' left_left right_left /\
          combine_fuel_sufficient fuel' left_right right_right /\
          combine_fuel_sufficient fuel' left_left right /\
          combine_fuel_sufficient fuel' left_right right /\
          combine_fuel_sufficient fuel' left right_left /\
          combine_fuel_sufficient fuel' left right_right
      | _, _ => True
      end
  end.

Lemma combine_fuel_sufficient_succ:
  forall (A B : Type) fuel (left : t A) (right : t B),
    combine_fuel_sufficient fuel left right ->
    combine_fuel_sufficient (S fuel) left right.
Proof.
  intros A B fuel. induction fuel as [|fuel IH]; intros left right H;
    [contradiction|].
  destruct left as [|left_key left_value|left_sample left_split left_left left_right];
    destruct right as [|right_key right_value|right_sample right_split right_left right_right];
    cbn in *; auto.
  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]]. repeat split.
  - exact (IH left_left right_left H1).
  - exact (IH left_right right_right H2).
  - exact (IH left_left (Branch right_sample right_split right_left right_right) H3).
  - exact (IH left_right (Branch right_sample right_split right_left right_right) H4).
  - exact (IH (Branch left_sample left_split left_left left_right) right_left H5).
  - exact (IH (Branch left_sample left_split left_left left_right) right_right H6).
Qed.

Lemma combine_fuel_sufficient_monotone:
  forall (A B : Type) fuel extra (left : t A) (right : t B),
    combine_fuel_sufficient fuel left right ->
    combine_fuel_sufficient (fuel + extra) left right.
Proof.
  intros A B fuel extra. induction extra as [|extra IH]; intros left right H.
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r. apply combine_fuel_sufficient_succ. now apply IH.
Qed.

Theorem public_combine_fuel_sufficient:
  forall (A B : Type) (left : t A) (right : t B),
    combine_fuel_sufficient (S (size left + size right)) left right.
Proof.
  intros A B.
  assert (Hstrong : forall total,
      forall (left : t A) (right : t B),
      size left + size right = total ->
      combine_fuel_sufficient (S total) left right).
  { intro total. induction total using lt_wf_ind.
    intros left right E. destruct left as
        [|left_key left_value|left_sample left_split left_left left_right];
      destruct right as
        [|right_key right_value|right_sample right_split right_left right_right];
      cbn; auto.
    repeat split.
    - pose proof (H (size left_left + size right_left)) as IH.
      assert (Hs := IH ltac:(cbn in E; lia) left_left right_left eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size left_right + S (size right_right)) _ _ Hs) as Hm.
      replace total with
        (S (size left_left + size right_left) +
         (size left_right + S (size right_right))) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size left_right + size right_right)) as IH.
      assert (Hs := IH ltac:(cbn in E; lia) left_right right_right eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size left_left + S (size right_left)) _ _ Hs) as Hm.
      replace total with
        (S (size left_right + size right_right) +
         (size left_left + S (size right_left))) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size left_left + size
        (Branch right_sample right_split right_left right_right))) as IH.
      assert (Hlt : size left_left +
        size (Branch right_sample right_split right_left right_right) < total) by
        (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt left_left
        (Branch right_sample right_split right_left right_right) eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size left_right) _ _ Hs) as Hm.
      replace total with
        (S (size left_left + size
          (Branch right_sample right_split right_left right_right)) +
         size left_right) by (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size left_right + size
        (Branch right_sample right_split right_left right_right))) as IH.
      assert (Hlt : size left_right +
        size (Branch right_sample right_split right_left right_right) < total) by
        (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt left_right
        (Branch right_sample right_split right_left right_right) eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size left_left) _ _ Hs) as Hm.
      replace total with
        (S (size left_right + size
          (Branch right_sample right_split right_left right_right)) +
         size left_left) by (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size (Branch left_sample left_split left_left left_right) +
        size right_left)) as IH.
      assert (Hlt : size (Branch left_sample left_split left_left left_right) +
        size right_left < total) by (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt
        (Branch left_sample left_split left_left left_right) right_left eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size right_right) _ _ Hs) as Hm.
      replace total with
        (S (size (Branch left_sample left_split left_left left_right) +
          size right_left) + size right_right) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size (Branch left_sample left_split left_left left_right) +
        size right_right)) as IH.
      assert (Hlt : size (Branch left_sample left_split left_left left_right) +
        size right_right < total) by (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt
        (Branch left_sample left_split left_left left_right) right_right eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size right_left) _ _ Hs) as Hm.
      replace total with
        (S (size (Branch left_sample left_split left_left left_right) +
          size right_right) + size right_left) by
        (cbn [size] in E |- *; lia). exact Hm. }
  intros. apply Hstrong with (total := size left + size right). reflexivity.
Qed.

Lemma branch_at_wf:
  forall (A : Type) sample split (fresh old : t A),
    wf fresh -> wf old ->
    representative fresh <> None -> representative old <> None ->
    all_keys (fun stored =>
      same_prefix sample stored split /\
      bit_at stored split = bit_at sample split) fresh ->
    all_keys (fun stored =>
      same_prefix sample stored split /\
      bit_at stored split = negb (bit_at sample split)) old ->
    wf (branch_at sample split fresh old).
Proof.
  intros A sample split fresh old Hfresh Hold Hfresh_nonempty Hold_nonempty
    Hfresh_keys Hold_keys.
  unfold branch_at. destruct (bit_at sample split) eqn:Esample.
  - apply wf_branch.
    + exact Hold.
    + exact Hfresh.
    + exact Hold_nonempty.
    + exact Hfresh_nonempty.
    + eapply all_keys_impl; [exact Hold_keys|].
      intros stored [Hprefix Hbit]. split; [exact Hprefix|exact Hbit].
    + eapply all_keys_impl; [exact Hfresh_keys|].
      intros stored [Hprefix Hbit]. split; [exact Hprefix|exact Hbit].
  - apply wf_branch.
    + exact Hfresh.
    + exact Hold.
    + exact Hfresh_nonempty.
    + exact Hold_nonempty.
    + eapply all_keys_impl; [exact Hfresh_keys|].
      intros stored [Hprefix Hbit]. split; [exact Hprefix|exact Hbit].
    + eapply all_keys_impl; [exact Hold_keys|].
      intros stored [Hprefix Hbit]. split; [exact Hprefix|exact Hbit].
Qed.

Lemma get_branch_at:
  forall (A : Type) sample split (fresh old : t A) query,
    all_keys (fun stored =>
      bit_at stored split = bit_at sample split) fresh ->
    all_keys (fun stored =>
      bit_at stored split = negb (bit_at sample split)) old ->
    get query (branch_at sample split fresh old) =
      match get query fresh with Some value => Some value | None => get query old end.
Proof.
  intros A sample split fresh old query Hfresh Hold.
  unfold branch_at. destruct (bit_at sample split) eqn:Esample;
    destruct (bit_at query split) eqn:Equery; cbn [get]; rewrite Equery.
  - destruct (get query fresh) eqn:Efresh; [reflexivity|].
    assert (Eold : get query old = None).
    { apply (get_none_if_all_keys A
        (fun stored => bit_at stored split = false) old query).
      - exact Hold.
      - intros Hbit. rewrite Equery in Hbit. discriminate. }
    now rewrite Eold.
  - assert (Efresh : get query fresh = None).
    { apply (get_none_if_all_keys A
        (fun stored => bit_at stored split = true) fresh query).
      - exact Hfresh.
      - intros Hbit. rewrite Equery in Hbit. discriminate. }
    now rewrite Efresh.
  - assert (Efresh : get query fresh = None).
    { apply (get_none_if_all_keys A
        (fun stored => bit_at stored split = false) fresh query).
      - exact Hfresh.
      - intros Hbit. rewrite Equery in Hbit. discriminate. }
    now rewrite Efresh.
  - destruct (get query fresh) eqn:Efresh; [reflexivity|].
    assert (Eold : get query old = None).
    { apply (get_none_if_all_keys A
        (fun stored => bit_at stored split = true) old query).
      - exact Hold.
      - intros Hbit. rewrite Equery in Hbit. discriminate. }
    now rewrite Eold.
Qed.

Theorem join_disjoint_correct_wf:
  forall (A : Type) (fresh old : t A) fresh_key old_key split,
    wf fresh -> wf old ->
    representative fresh = Some fresh_key ->
    representative old = Some old_key ->
    first_diff fresh_key old_key = Some split ->
    all_keys (fun stored =>
      same_prefix fresh_key stored split /\
      bit_at stored split = bit_at fresh_key split) fresh ->
    all_keys (fun stored =>
      same_prefix fresh_key stored split /\
      bit_at stored split = negb (bit_at fresh_key split)) old ->
    wf (join fresh old) /\
    forall query,
      get query (join fresh old) =
        match get query fresh with Some value => Some value | None => get query old end.
Proof.
  intros A fresh old fresh_key old_key split Hfresh Hold Hfresh_rep Hold_rep
    Hdiff Hfresh_keys Hold_keys.
  unfold join. rewrite Hfresh_rep, Hold_rep, Hdiff.
  split.
  - apply branch_at_wf; try assumption; congruence.
  - intro query. apply get_branch_at.
    + eapply all_keys_impl; [exact Hfresh_keys|].
      intros stored H. exact (proj2 H).
    + eapply all_keys_impl; [exact Hold_keys|].
      intros stored H. exact (proj2 H).
Qed.

(** [join] also handles an empty filtered side.  This version of the disjoint
    join law therefore supplies the form required by generic merge, while
    delegating the non-empty case to [join_disjoint_correct_wf]. *)
Theorem join_separated_correct_wf:
  forall (A : Type) sample split (fresh old : t A),
    wf fresh -> wf old ->
    all_keys (fun stored =>
      same_prefix sample stored split /\
      bit_at stored split = bit_at sample split) fresh ->
    all_keys (fun stored =>
      same_prefix sample stored split /\
      bit_at stored split = negb (bit_at sample split)) old ->
    wf (join fresh old) /\
    forall query,
      get query (join fresh old) =
        match get query fresh with Some value => Some value | None => get query old end.
Proof.
  intros A sample split fresh old Hfresh Hold Hfresh_keys Hold_keys.
  destruct (representative fresh) as [fresh_key|] eqn:Efresh;
    destruct (representative old) as [old_key|] eqn:Eold.
  - pose proof (representative_all_keys A _ fresh fresh_key Hfresh_keys Efresh)
      as [Hfresh_prefix Hfresh_bit].
    pose proof (representative_all_keys A _ old old_key Hold_keys Eold)
      as [Hold_prefix Hold_bit].
    assert (Hfirst : first_diff fresh_key old_key = Some split).
    { apply first_diff_at.
      - eapply same_prefix_rebase; eauto.
      - rewrite Hfresh_bit, Hold_bit. destruct (bit_at sample split);
          discriminate. }
    assert (Hfresh_separated : all_keys (fun stored =>
      same_prefix fresh_key stored split /\
      bit_at stored split = bit_at fresh_key split) fresh).
    { eapply all_keys_impl; [exact Hfresh_keys|]. intros stored [Hprefix Hbit].
      split.
      - eapply same_prefix_rebase; eauto.
      - now rewrite Hbit, Hfresh_bit. }
    assert (Hold_separated : all_keys (fun stored =>
      same_prefix fresh_key stored split /\
      bit_at stored split = negb (bit_at fresh_key split)) old).
    { eapply all_keys_impl; [exact Hold_keys|]. intros stored [Hprefix Hbit].
      split.
      - eapply same_prefix_rebase; eauto.
      - now rewrite Hbit, Hfresh_bit. }
    eapply join_disjoint_correct_wf; eauto.
  - pose proof (wf_representative_none A old Hold Eold) as Eempty. subst old.
    unfold join. rewrite Efresh. cbn. split; [exact Hfresh|].
    intro query. now destruct (get query fresh).
  - pose proof (wf_representative_none A fresh Hfresh Efresh) as Eempty. subst fresh.
    cbn [join]. split; [exact Hold|reflexivity].
  - pose proof (wf_representative_none A fresh Hfresh Efresh) as Eempty. subst fresh.
    cbn [join]. split; [exact Hold|reflexivity].
Qed.

(** Functional merge laws preserve any key predicate already satisfied by
    both inputs.  The target tree's [wf] proof bridges routed lookup back to
    its structural [all_keys] invariant. *)
Lemma all_keys_of_combine_lookup:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (left : t A) (right : t B) (out : t C) (P : string -> Prop),
    f None None = None -> wf out ->
    (forall key, get key out = f (get key left) (get key right)) ->
    all_keys P left -> all_keys P right -> all_keys P out.
Proof.
  intros A B C f left right out P Hnone Hwout Hget Hleft Hright.
  apply (proj2 (all_keys_elements C P out)).
  intros key value Hin.
  pose proof (wf_elements_complete C out Hwout key value Hin) as Hout.
  specialize (Hget key).
  destruct (get key left) as [left_value|] eqn:Eleft;
    destruct (get key right) as [right_value|] eqn:Eright.
  - eapply (all_keys_get A P left key left_value); eauto.
  - eapply (all_keys_get A P left key left_value); eauto.
  - eapply (all_keys_get B P right key right_value); eauto.
  - rewrite Hnone in Hget. congruence.
Qed.

Lemma all_keys_map_left:
  forall (A B C : Type) (P : string -> Prop)
      (f : option A -> option B -> option C) (m : t A),
    all_keys P m -> all_keys P (map_left f m).
Proof.
  intros. unfold map_left. now apply all_keys_map_filter.
Qed.

Lemma all_keys_map_right:
  forall (A B C : Type) (P : string -> Prop)
      (f : option A -> option B -> option C) (m : t B),
    all_keys P m -> all_keys P (map_right f m).
Proof.
  intros. unfold map_right. now apply all_keys_map_filter.
Qed.

(** Once two inputs are separated at one bit, their one-sided maps remain
    separated.  Consequently [join] implements the generic merge law: the
    apparently left-biased lookup cannot discard a right result because no
    key can occur in both inputs. *)
Lemma combine_join_separated_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      sample split (left : t A) (right : t B),
    f None None = None -> wf left -> wf right ->
    all_keys (fun key =>
      same_prefix sample key split /\
      bit_at key split = bit_at sample split) left ->
    all_keys (fun key =>
      same_prefix sample key split /\
      bit_at key split = negb (bit_at sample split)) right ->
    wf (join (map_left f left) (map_right f right)) /\
    forall key,
      get key (join (map_left f left) (map_right f right)) =
      f (get key left) (get key right).
Proof.
  intros A B C f sample split left right Hnone Hwl Hwr Hleft Hright.
  destruct (@map_left_correct_wf A B C f left Hnone Hwl) as [Hwml Hml].
  destruct (@map_right_correct_wf A B C f right Hnone Hwr) as [Hwmr Hmr].
  assert (Hmapped_left : all_keys (fun key =>
      same_prefix sample key split /\
      bit_at key split = bit_at sample split) (map_left f left)).
  { eapply all_keys_map_left. exact Hleft. }
  assert (Hmapped_right : all_keys (fun key =>
      same_prefix sample key split /\
      bit_at key split = negb (bit_at sample split)) (map_right f right)).
  { eapply all_keys_map_right. exact Hright. }
  destruct (join_separated_correct_wf C sample split
    (map_left f left) (map_right f right)
    Hwml Hwmr Hmapped_left Hmapped_right) as [Hwj Hjoin].
  split; [exact Hwj|]. intro key. rewrite Hjoin, Hml, Hmr.
  destruct (get key left) as [left_value|] eqn:Eleft;
    destruct (get key right) as [right_value|] eqn:Eright.
  - pose proof (all_keys_get A _ left key left_value Hleft Eleft)
      as [_ Hleft_bit].
    pose proof (all_keys_get B _ right key right_value Hright Eright)
      as [_ Hright_bit].
    exfalso. rewrite Hleft_bit in Hright_bit.
    now destruct (bit_at sample split) in Hright_bit.
  - now destruct (f (Some left_value) None).
  - now rewrite Hnone.
  - now rewrite Hnone.
Qed.

Theorem combine_fuel_correct_wf:
  forall (A B C : Type) fuel
      (f : option A -> option B -> option C) (left : t A) (right : t B),
    f None None = None ->
    wf left -> wf right ->
    combine_fuel_sufficient fuel left right ->
    wf (combine_fuel fuel f left right) /\
    forall key,
      get key (combine_fuel fuel f left right) =
      f (get key left) (get key right).
Proof.
  intros A B C fuel. induction fuel as [|fuel IH];
    intros f left right Hnone Hwl Hwr Hfuel; [contradiction|].
  destruct left as [|left_key left_value
      |left_sample left_split left_left left_right];
    destruct right as [|right_key right_value
      |right_sample right_split right_left right_right].
  - cbn [combine_fuel map_right map_filter get].
    split; [constructor|]. intro key. symmetry. exact Hnone.
  - cbn [combine_fuel]. now apply map_right_correct_wf.
  - cbn [combine_fuel]. now apply map_right_correct_wf.
  - cbn [combine_fuel]. now apply map_left_correct_wf.
  - cbn [combine_fuel]. now apply combine_leaf_left_correct_wf.
  - cbn [combine_fuel]. now apply combine_leaf_left_correct_wf.
  - cbn [combine_fuel]. now apply map_left_correct_wf.
  - cbn [combine_fuel]. now apply combine_leaf_right_correct_wf.
  - cbn in Hfuel.
    destruct Hfuel as [Hsll [Hsrr [Hslall [Hslarr [Hsal Hsar]]]]].
    inversion Hwl as
      [| |? ? ? ? Hwll Hwlr Hnell Hnelr Hall Halr]; subst.
    inversion Hwr as
      [| |? ? ? ? Hwrl Hwrr Hnerl Hnerr Harl Harr]; subst.
    cbn [combine_fuel].
    destruct (left_split =? right_split) eqn:Esplits.
    + apply Nat.eqb_eq in Esplits. subst right_split.
      destruct (agrees_before_bounded left_sample right_sample left_split)
        eqn:Eagrees.
      * pose proof ((proj1 (agrees_before_bounded_spec
          left_sample right_sample left_split)) Eagrees) as Hsamples.
        destruct (IH f left_left right_left Hnone Hwll Hwrl Hsll)
          as [Hwoutl Hgetoutl].
        destruct (IH f left_right right_right Hnone Hwlr Hwrr Hsrr)
          as [Hwoutr Hgetoutr].
        assert (Harl' : all_keys (fun key =>
            same_prefix left_sample key left_split /\
            bit_at key left_split = false) right_left).
        { eapply all_keys_equal_split_rebase; eauto. }
        assert (Harr' : all_keys (fun key =>
            same_prefix left_sample key left_split /\
            bit_at key left_split = true) right_right).
        { eapply all_keys_equal_split_rebase; eauto. }
        assert (Houtl : all_keys (fun key =>
            same_prefix left_sample key left_split /\
            bit_at key left_split = false)
            (combine_fuel fuel f left_left right_left)).
        { eapply all_keys_of_combine_lookup; eauto. }
        assert (Houtr : all_keys (fun key =>
            same_prefix left_sample key left_split /\
            bit_at key left_split = true)
            (combine_fuel fuel f left_right right_right)).
        { eapply all_keys_of_combine_lookup; eauto. }
        split.
        -- now apply branch_wf_general.
        -- intro key.
           rewrite get_branch.
           ++ cbn [get]. destruct (bit_at key left_split);
                [apply Hgetoutr|apply Hgetoutl].
           ++ eapply all_keys_impl; [exact Houtl|].
              intros stored H. exact (proj2 H).
           ++ eapply all_keys_impl; [exact Houtr|].
              intros stored H. exact (proj2 H).
      * assert (Emin : Nat.min left_split left_split = left_split) by
          apply Nat.min_id.
        destruct (branches_disjoint_prefix A B left_sample left_split
          (Branch left_sample left_split left_left left_right)
          right_sample left_split
          (Branch right_sample left_split right_left right_right)
          (branch_all_prefix A left_sample left_split left_left left_right
            Hall Halr)
          (branch_all_prefix B right_sample left_split right_left right_right
            Harl Harr)) as [differing [Hdiff [Hleft Hright]]].
        -- now rewrite Emin.
        -- eapply combine_join_separated_correct_wf; eauto.
    + destruct (left_split <? right_split) eqn:Eorder.
      * apply Nat.ltb_lt in Eorder.
        destruct (agrees_before_bounded left_sample right_sample left_split)
          eqn:Eagrees.
        -- pose proof ((proj1 (agrees_before_bounded_spec
             left_sample right_sample left_split)) Eagrees) as Hsamples.
           assert (Hright_prefix : all_keys
             (fun key => same_prefix right_sample key right_split)
             (Branch right_sample right_split right_left right_right)).
           { now apply branch_all_prefix. }
           assert (Hcontained : all_keys (fun key =>
               same_prefix left_sample key left_split /\
               bit_at key left_split = bit_at right_sample left_split)
               (Branch right_sample right_split right_left right_right)).
           { eapply all_keys_contained_prefix; eauto. }
           destruct (bit_at right_sample left_split) eqn:Eside.
           ++ destruct (@map_left_correct_wf A B C f left_left Hnone Hwll)
                as [Hwmap Hgetmap].
              destruct (IH f left_right
                (Branch right_sample right_split right_left right_right)
                Hnone Hwlr Hwr Hslarr) as [Hwout Hgetout].
              assert (Hmap : all_keys (fun key =>
                  same_prefix left_sample key left_split /\
                  bit_at key left_split = false) (map_left f left_left)).
              { eapply all_keys_map_left. exact Hall. }
              assert (Hout : all_keys (fun key =>
                  same_prefix left_sample key left_split /\
                  bit_at key left_split = true)
                  (combine_fuel fuel f left_right
                    (Branch right_sample right_split right_left right_right))).
              { eapply all_keys_of_combine_lookup; eauto. }
              split.
              ** now apply branch_wf_general.
              ** intro key. rewrite get_branch.
                 --- change
                       ((if bit_at key left_split
                         then get key (combine_fuel fuel f left_right
                           (Branch right_sample right_split
                             right_left right_right))
                         else get key (map_left f left_left)) =
                        f (if bit_at key left_split
                           then get key left_right else get key left_left)
                          (get key (Branch right_sample right_split
                            right_left right_right))).
                     destruct (bit_at key left_split) eqn:Ekey.
                     +++ rewrite (Hgetout key). reflexivity.
                     +++ rewrite Hgetmap.
                       assert (Eright : get key
                         (Branch right_sample right_split right_left right_right) =
                         None).
                       { eapply get_none_if_all_keys; [exact Hcontained|].
                         intros [_ Hbit]. rewrite Ekey in Hbit.
                         discriminate. }
                       now rewrite Eright.
                 --- eapply all_keys_impl; [exact Hmap|].
                     intros stored H. exact (proj2 H).
                 --- eapply all_keys_impl; [exact Hout|].
                     intros stored H. exact (proj2 H).
           ++ destruct (IH f left_left
                (Branch right_sample right_split right_left right_right)
                Hnone Hwll Hwr Hslall) as [Hwout Hgetout].
              destruct (@map_left_correct_wf A B C f left_right Hnone Hwlr)
                as [Hwmap Hgetmap].
              assert (Hout : all_keys (fun key =>
                  same_prefix left_sample key left_split /\
                  bit_at key left_split = false)
                  (combine_fuel fuel f left_left
                    (Branch right_sample right_split right_left right_right))).
              { eapply all_keys_of_combine_lookup; eauto. }
              assert (Hmap : all_keys (fun key =>
                  same_prefix left_sample key left_split /\
                  bit_at key left_split = true) (map_left f left_right)).
              { eapply all_keys_map_left. exact Halr. }
              split.
              ** now apply branch_wf_general.
              ** intro key. rewrite get_branch.
                 --- change
                       ((if bit_at key left_split
                         then get key (map_left f left_right)
                         else get key (combine_fuel fuel f left_left
                           (Branch right_sample right_split
                             right_left right_right))) =
                        f (if bit_at key left_split
                           then get key left_right else get key left_left)
                          (get key (Branch right_sample right_split
                            right_left right_right))).
                     destruct (bit_at key left_split) eqn:Ekey.
                     +++ rewrite Hgetmap.
                       assert (Eright : get key
                         (Branch right_sample right_split right_left right_right) =
                         None).
                       { eapply get_none_if_all_keys; [exact Hcontained|].
                         intros [_ Hbit]. rewrite Ekey in Hbit.
                         discriminate. }
                       now rewrite Eright.
                     +++ rewrite (Hgetout key). reflexivity.
                 --- eapply all_keys_impl; [exact Hout|].
                     intros stored H. exact (proj2 H).
                 --- eapply all_keys_impl; [exact Hmap|].
                     intros stored H. exact (proj2 H).
        -- assert (Emin : Nat.min left_split right_split = left_split) by
             (apply Nat.min_l; lia).
           destruct (branches_disjoint_prefix A B left_sample left_split
             (Branch left_sample left_split left_left left_right)
             right_sample right_split
             (Branch right_sample right_split right_left right_right)
             (branch_all_prefix A left_sample left_split left_left left_right
               Hall Halr)
             (branch_all_prefix B right_sample right_split right_left right_right
               Harl Harr)) as [differing [Hdiff [Hleft Hright]]].
           ++ now rewrite Emin.
           ++ eapply combine_join_separated_correct_wf; eauto.
      * apply Nat.ltb_ge in Eorder.
        assert (Hreverse : right_split < left_split) by
          (apply Nat.eqb_neq in Esplits; lia).
        destruct (agrees_before_bounded left_sample right_sample right_split)
          eqn:Eagrees.
        -- pose proof ((proj1 (agrees_before_bounded_spec
             left_sample right_sample right_split)) Eagrees) as Hsamples.
           assert (Hleft_prefix : all_keys
             (fun key => same_prefix left_sample key left_split)
             (Branch left_sample left_split left_left left_right)).
           { now apply branch_all_prefix. }
           assert (Hcontained : all_keys (fun key =>
               same_prefix right_sample key right_split /\
               bit_at key right_split = bit_at left_sample right_split)
               (Branch left_sample left_split left_left left_right)).
           { eapply all_keys_contained_prefix; eauto.
             unfold same_prefix in *. intros n Hn.
             symmetry. now apply Hsamples. }
           destruct (bit_at left_sample right_split) eqn:Eside.
           ++ destruct (@map_right_correct_wf A B C f right_left Hnone Hwrl)
                as [Hwmap Hgetmap].
              destruct (IH f
                (Branch left_sample left_split left_left left_right)
                right_right Hnone Hwl Hwrr Hsar) as [Hwout Hgetout].
              assert (Hmap : all_keys (fun key =>
                  same_prefix right_sample key right_split /\
                  bit_at key right_split = false) (map_right f right_left)).
              { eapply all_keys_map_right. exact Harl. }
              assert (Hout : all_keys (fun key =>
                  same_prefix right_sample key right_split /\
                  bit_at key right_split = true)
                  (combine_fuel fuel f
                    (Branch left_sample left_split left_left left_right)
                    right_right)).
              { eapply all_keys_of_combine_lookup; eauto. }
              split.
              ** now apply branch_wf_general.
              ** intro key. rewrite get_branch.
                 --- change
                       ((if bit_at key right_split
                         then get key (combine_fuel fuel f
                           (Branch left_sample left_split left_left left_right)
                           right_right)
                         else get key (map_right f right_left)) =
                        f (get key (Branch left_sample left_split
                             left_left left_right))
                          (if bit_at key right_split
                           then get key right_right else get key right_left)).
                     destruct (bit_at key right_split) eqn:Ekey.
                     +++ rewrite (Hgetout key). reflexivity.
                     +++ rewrite Hgetmap.
                       assert (Eleft : get key
                         (Branch left_sample left_split left_left left_right) =
                         None).
                       { eapply get_none_if_all_keys; [exact Hcontained|].
                         intros [_ Hbit]. rewrite Ekey in Hbit.
                         discriminate. }
                       now rewrite Eleft.
                 --- eapply all_keys_impl; [exact Hmap|].
                     intros stored H. exact (proj2 H).
                 --- eapply all_keys_impl; [exact Hout|].
                     intros stored H. exact (proj2 H).
           ++ destruct (IH f
                (Branch left_sample left_split left_left left_right)
                right_left Hnone Hwl Hwrl Hsal) as [Hwout Hgetout].
              destruct (@map_right_correct_wf A B C f right_right Hnone Hwrr)
                as [Hwmap Hgetmap].
              assert (Hout : all_keys (fun key =>
                  same_prefix right_sample key right_split /\
                  bit_at key right_split = false)
                  (combine_fuel fuel f
                    (Branch left_sample left_split left_left left_right)
                    right_left)).
              { eapply all_keys_of_combine_lookup; eauto. }
              assert (Hmap : all_keys (fun key =>
                  same_prefix right_sample key right_split /\
                  bit_at key right_split = true) (map_right f right_right)).
              { eapply all_keys_map_right. exact Harr. }
              split.
              ** now apply branch_wf_general.
              ** intro key. rewrite get_branch.
                 --- change
                       ((if bit_at key right_split
                         then get key (map_right f right_right)
                         else get key (combine_fuel fuel f
                           (Branch left_sample left_split left_left left_right)
                           right_left)) =
                        f (get key (Branch left_sample left_split
                             left_left left_right))
                          (if bit_at key right_split
                           then get key right_right else get key right_left)).
                     destruct (bit_at key right_split) eqn:Ekey.
                     +++ rewrite Hgetmap.
                       assert (Eleft : get key
                         (Branch left_sample left_split left_left left_right) =
                         None).
                       { eapply get_none_if_all_keys; [exact Hcontained|].
                         intros [_ Hbit]. rewrite Ekey in Hbit.
                         discriminate. }
                       now rewrite Eleft.
                     +++ rewrite (Hgetout key). reflexivity.
                 --- eapply all_keys_impl; [exact Hout|].
                     intros stored H. exact (proj2 H).
                 --- eapply all_keys_impl; [exact Hmap|].
                     intros stored H. exact (proj2 H).
        -- assert (Emin : Nat.min left_split right_split = right_split) by
             (apply Nat.min_r; lia).
           destruct (branches_disjoint_prefix A B left_sample left_split
             (Branch left_sample left_split left_left left_right)
             right_sample right_split
             (Branch right_sample right_split right_left right_right)
             (branch_all_prefix A left_sample left_split left_left left_right
               Hall Halr)
             (branch_all_prefix B right_sample right_split right_left right_right
               Harl Harr)) as [differing [Hdiff [Hleft Hright]]].
           ++ now rewrite Emin.
           ++ eapply combine_join_separated_correct_wf; eauto.
Qed.

Theorem combine_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (left : t A) (right : t B),
    f None None = None -> wf left -> wf right ->
    wf (combine f left right) /\
    forall key,
      get key (combine f left right) = f (get key left) (get key right).
Proof.
  intros. unfold combine. eapply combine_fuel_correct_wf; eauto.
  apply public_combine_fuel_sufficient.
Qed.

Theorem union_left_correct_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    wf (union_left left right) /\
    forall key,
      get key (union_left left right) =
      match get key left with
      | Some value => Some value
      | None => get key right
      end.
Proof.
  intros A left right Hleft Hright.
  unfold union_left.
  destruct (combine_correct_wf A A A
    (fun x y => match x with Some _ => x | None => y end)
    left right eq_refl Hleft Hright) as [Hwf Hget].
  split; [exact Hwf|].
  intro key. rewrite Hget.
  now destruct (get key left).
Qed.

Theorem union_right_correct_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    wf (union_right left right) /\
    forall key,
      get key (union_right left right) =
      match get key right with
      | Some value => Some value
      | None => get key left
      end.
Proof.
  intros A left right Hleft Hright.
  unfold union_right.
  destruct (combine_correct_wf A A A
    (fun x y => match y with Some _ => y | None => x end)
    left right eq_refl Hleft Hright) as [Hwf Hget].
  split; [exact Hwf|].
  intro key. rewrite Hget.
  now destruct (get key right).
Qed.

Definition sample : t nat :=
  set "alpha" 1 (set "alphabet" 2 (set "" 3 (set "beta" 4 empty)))%string.

Example lookup_empty_string: get "" sample = Some 3%nat.
Proof. vm_compute. reflexivity. Qed.

Example lookup_prefix_key: get "alpha" sample = Some 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example lookup_extension_key: get "alphabet" sample = Some 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example remove_prefix_preserves_extension:
  get "alphabet" (remove "alpha" sample) = Some 2%nat.
Proof. vm_compute. reflexivity. Qed.
