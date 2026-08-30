(** Focused correctness results and executable regression cases for the
    standalone prototype.  The invariant is intentionally separate from the
    runtime tree type. *)

From Stdlib Require Import Arith.Wf_nat Bool Lia List NArith PArith PeanoNat.
Import ListNotations.

Require Import PatriciaBits Patricia.

Set Implicit Arguments.

Definition nonempty {A : Type} (m : t A) : Prop :=
  exists k v, get k m = Some v.

Definition all_keys {A : Type} (P : positive -> Prop) (m : t A) : Prop :=
  forall k v, get k m = Some v -> P k.

Inductive wf {A : Type} : t A -> Prop :=
| wf_empty : wf Empty
| wf_leaf : forall k v, wf (Leaf k v)
| wf_branch : forall p mask l r,
    wf l -> wf r ->
    nonempty l -> nonempty r ->
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = true) l ->
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = false) r ->
    wf (Branch p mask l r).

(** Finite-map equality is observational equality of lookup, not structural
    equality of Patricia trees. *)
Definition equiv {A : Type} (left right : t A) : Prop :=
  forall key, get key left = get key right.

Lemma equiv_refl:
  forall (A : Type) (m : t A), equiv m m.
Proof. intros A m key. reflexivity. Qed.

Lemma equiv_sym:
  forall (A : Type) (left right : t A),
    equiv left right -> equiv right left.
Proof. intros A left right H key. symmetry. apply H. Qed.

Lemma equiv_trans:
  forall (A : Type) (left middle right : t A),
    equiv left middle -> equiv middle right -> equiv left right.
Proof. intros A left middle right Hlm Hmr key. rewrite Hlm. apply Hmr. Qed.

Lemma get_empty:
  forall (A : Type) k, @get A k empty = None.
Proof. reflexivity. Qed.

Lemma get_singleton_same:
  forall (A : Type) k (v : A), get k (singleton k v) = Some v.
Proof.
  intros. simpl. now rewrite Pos.eqb_refl.
Qed.

Lemma get_singleton_other:
  forall (A : Type) i j (v : A),
    i <> j -> get i (singleton j v) = None.
Proof.
  intros. simpl. apply Pos.eqb_neq in H. now rewrite H.
Qed.

Lemma mem_get:
  forall (A : Type) k (m : t A),
    mem k m = match get k m with Some _ => true | None => false end.
Proof.
  intros A k m. induction m as [|j value|p mask ltree IHl rtree IHr]; cbn.
  - reflexivity.
  - now destruct (Pos.eqb k j).
  - destruct (matches_prefix k p mask); cbn; [|reflexivity].
    now destruct (zero_bit k mask).
Qed.

Lemma mem_spec:
  forall (A : Type) k (m : t A),
    mem k m = true <-> exists v, get k m = Some v.
Proof.
  intros A k m. rewrite mem_get. destruct (get k m) eqn:E; split; intros H.
  - now exists a.
  - reflexivity.
  - discriminate.
  - destruct H as [v H]. congruence.
Qed.

Lemma is_empty_spec:
  forall (A : Type) (m : t A), is_empty m = true <-> m = Empty.
Proof.
  intros A m. destruct m as [|key value|prefix mask ltree rtree]; cbn.
  - split; intros H; reflexivity.
  - split; [discriminate|intros H; discriminate].
  - split; [discriminate|intros H; discriminate].
Qed.

Lemma representative_singleton:
  forall (A : Type) k (v : A), representative (singleton k v) = Some k.
Proof. reflexivity. Qed.

Lemma join_singleton_left_get:
  forall (A : Type) k (v : A) (m : t A),
    get k (join (singleton k v) m) = Some v.
Proof.
  intros A k v m. unfold join, singleton. simpl.
  destruct (representative m) as [j|] eqn:R; simpl.
  - destruct (Pos.eqb k j) eqn:E.
    + simpl. now rewrite Pos.eqb_refl.
    + destruct (zero_bit k (highest_differing_bit k j)) eqn:Z;
        cbn [get]; rewrite matches_prefix_refl, Z; cbn [get];
        now rewrite Pos.eqb_refl.
  - simpl. now rewrite Pos.eqb_refl.
Qed.

Lemma get_set_same:
  forall (A : Type) k (v : A) (m : t A),
    get k (set k v m) = Some v.
Proof.
  intros A k v m. induction m as [|j old|p mask l IHl r IHr].
  - cbn. now rewrite Pos.eqb_refl.
  - destruct (Pos.eqb k j) eqn:E.
    + cbn [set get]. rewrite E. cbn. now rewrite Pos.eqb_refl.
    + cbn [set]. rewrite E. apply join_singleton_left_get.
  - destruct (matches_prefix k p mask) eqn:P.
    + destruct (zero_bit k mask) eqn:Z.
      * cbn [set]. rewrite P, Z. cbn [get]. rewrite P, Z. exact IHl.
      * cbn [set]. rewrite P, Z. cbn [get]. rewrite P, Z. exact IHr.
    + cbn [set]. rewrite P. apply join_singleton_left_get.
Qed.

Lemma get_map:
  forall (A B : Type) (f : positive -> A -> B) k (m : t A),
    get k (map f m) = option_map (f k) (get k m).
Proof.
  intros A B f k m. induction m as [|j v|p mask l IHl r IHr]; simpl.
  - reflexivity.
  - destruct (Pos.eqb k j) eqn:E; simpl.
    + apply Pos.eqb_eq in E. now subst.
    + reflexivity.
  - destruct (matches_prefix k p mask); [destruct (zero_bit k mask)|];
      simpl; assumption || reflexivity.
Qed.

Lemma nonempty_map:
  forall (A B : Type) (f : positive -> A -> B) (m : t A),
    nonempty m -> nonempty (map f m).
Proof.
  intros A B f m [key [value Hget]].
  exists key, (f key value). rewrite get_map, Hget. reflexivity.
Qed.

Lemma all_keys_map:
  forall (A B : Type) (f : positive -> A -> B)
      (P : positive -> Prop) (m : t A),
    all_keys P m -> all_keys P (map f m).
Proof.
  intros A B f P m Hall key value Hget.
  rewrite get_map in Hget.
  destruct (get key m) as [old|] eqn:E; cbn in Hget; [|discriminate].
  apply (Hall key old E).
Qed.

Theorem map_wf:
  forall (A B : Type) (f : positive -> A -> B) (m : t A),
    wf m -> wf (map f m).
Proof.
  intros A B f m Hwf. induction Hwf; cbn [map].
  - constructor.
  - constructor.
  - constructor; eauto using nonempty_map, all_keys_map.
Qed.

Lemma elements_aux_spec:
  forall (A : Type) (m : t A) tail,
    elements_aux m tail = elements m ++ tail.
Proof.
  intros A m. induction m as [|key value|p mask ltree IHl rtree IHr];
    intros tail; cbn [elements].
  - reflexivity.
  - reflexivity.
  - change (elements_aux ltree (elements_aux rtree tail) =
      elements_aux ltree (elements_aux rtree []) ++ tail).
    rewrite !IHl, !IHr.
    now rewrite List.app_nil_r, List.app_assoc.
Qed.

Lemma elements_branch:
  forall (A : Type) p mask (ltree rtree : t A),
    elements (Branch p mask ltree rtree) = elements ltree ++ elements rtree.
Proof.
  intros. change (elements_aux ltree (elements_aux rtree []) =
    elements ltree ++ elements rtree).
  rewrite elements_aux_spec, elements_aux_spec.
  now rewrite List.app_nil_r.
Qed.

Lemma fold_elements:
  forall (A B : Type) (f : B -> positive -> A -> B) (m : t A) acc,
    fold f m acc =
    List.fold_left (fun a kv => f a (fst kv) (snd kv)) (elements m) acc.
Proof.
  intros A B f m. induction m as [|k v|p mask l IHl r IHr]; intros acc.
  - reflexivity.
  - reflexivity.
  - cbn [fold]. rewrite elements_branch, List.fold_left_app.
    now rewrite <- IHl, <- IHr.
Qed.

Lemma elements_sound:
  forall (A : Type) (m : t A) key value,
    get key m = Some value -> In (key, value) (elements m).
Proof.
  intros A m. induction m as [|stored data|p mask l IHl r IHr];
    intros key value Hget.
  - discriminate.
  - cbn [get elements elements_aux] in *.
    destruct (Pos.eqb key stored) eqn:E; inversion Hget; subst.
    apply Pos.eqb_eq in E. subst. now left.
  - cbn [get] in Hget. rewrite elements_branch.
    destruct (matches_prefix key p mask) eqn:P; try discriminate.
    destruct (zero_bit key mask) eqn:Z.
    + apply in_or_app. left. now apply IHl.
    + apply in_or_app. right. now apply IHr.
Qed.

Lemma elements_complete_wf:
  forall (A : Type) (m : t A), wf m ->
  forall key value, In (key, value) (elements m) -> get key m = Some value.
Proof.
  intros A m Hwf.
  induction Hwf as
      [|stored data|p mask l r Hwl IHl Hwr IHr Hnel Hner Hall Har];
    intros key value Hin.
  - cbn [elements elements_aux] in Hin. contradiction.
  - cbn [elements elements_aux] in Hin.
    destruct Hin as [Heq|[]]. inversion Heq; subst.
    cbn [get]. now rewrite Pos.eqb_refl.
  - rewrite elements_branch in Hin. cbn [get].
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + pose proof (IHl _ _ Hin) as Hget.
      pose proof (Hall _ _ Hget) as [P Z].
      now rewrite P, Z.
    + pose proof (IHr _ _ Hin) as Hget.
      pose proof (Har _ _ Hget) as [P Z].
      rewrite P, Z. exact Hget.
Qed.

Theorem elements_spec_wf:
  forall (A : Type) (m : t A), wf m ->
  forall key value,
    In (key, value) (elements m) <-> get key m = Some value.
Proof.
  intros. split.
  - now apply elements_complete_wf.
  - now apply elements_sound.
Qed.

Theorem equiv_elements_wf:
  forall (A : Type) (left right : t A),
    wf left -> wf right ->
    equiv left right <->
    forall key value,
      In (key, value) (elements left) <->
      In (key, value) (elements right).
Proof.
  intros A left right Hleft Hright. split.
  - intros Hequiv key value.
    rewrite (@elements_spec_wf A left Hleft key value),
      (@elements_spec_wf A right Hright key value).
    unfold equiv in Hequiv. now rewrite Hequiv.
  - intros Hbindings key. unfold equiv.
    destruct (get key left) as [left_value|] eqn:Eleft;
      destruct (get key right) as [right_value|] eqn:Eright;
      try reflexivity.
    + pose proof (proj1 (Hbindings key left_value)
        (@elements_sound A left key left_value Eleft)) as Hin.
      pose proof (@elements_complete_wf A right Hright key left_value Hin) as E.
      congruence.
    + pose proof (proj1 (Hbindings key left_value)
        (@elements_sound A left key left_value Eleft)) as Hin.
      pose proof (@elements_complete_wf A right Hright key left_value Hin) as E.
      congruence.
    + pose proof (proj2 (Hbindings key right_value)
        (@elements_sound A right key right_value Eright)) as Hin.
      pose proof (@elements_complete_wf A left Hleft key right_value Hin) as E.
      congruence.
Qed.

Theorem elements_keys_nodup_wf:
  forall (A : Type) (m : t A), wf m ->
    NoDup (List.map (@fst positive A) (elements m)).
Proof.
  intros A m Hwf.
  induction Hwf as
      [|stored data|p mask l r Hwl IHl Hwr IHr Hnel Hner Hall Har].
  - cbn [elements elements_aux]. constructor.
  - cbn [elements elements_aux].
    constructor; [intro H; inversion H|constructor].
  - rewrite elements_branch, List.map_app. apply NoDup_app; auto.
    intros key Hinl Hinr.
    apply in_map_iff in Hinl. destruct Hinl as [[kl vl] [Hkl Hinl]]. cbn in Hkl.
    apply in_map_iff in Hinr. destruct Hinr as [[kr vr] [Hkr Hinr]]. cbn in Hkr.
    subst kl kr.
    pose proof (@elements_complete_wf A l Hwl key vl Hinl) as Hgetl.
    pose proof (@elements_complete_wf A r Hwr key vr Hinr) as Hgetr.
    pose proof (Hall _ _ Hgetl) as [_ Zl].
    pose proof (Har _ _ Hgetr) as [_ Zr].
    congruence.
Qed.

Lemma forallb_elements:
  forall (A : Type) (test : positive -> A -> bool) (m : t A),
    forallb test m = true <->
    forall key value, In (key, value) (elements m) -> test key value = true.
Proof.
  intros A test m. induction m as [|key value|p mask l IHl r IHr].
  - cbn [forallb elements elements_aux].
    split; intros; [contradiction|reflexivity].
  - split.
    + cbn [forallb elements elements_aux].
      intros H k v [Heq|[]]. now inversion Heq; subst.
    + intros H. exact (H key value (or_introl eq_refl)).
  - cbn [forallb]. rewrite elements_branch, Bool.andb_true_iff, IHl, IHr.
    split.
    + intros [Hl Hr] key value Hin. apply in_app_or in Hin.
      destruct Hin; auto.
    + intros H. split; intros key value Hin; apply H; apply in_or_app; auto.
Qed.

Theorem beq_correct_wf:
  forall (A : Type) (eqA : A -> A -> bool) (left right : t A),
    wf left -> wf right ->
    beq eqA left right = true <->
    forall key,
      match get key left, get key right with
      | None, None => True
      | Some x, Some y => eqA x y = true
      | _, _ => False
      end.
Proof.
  intros A eqA left right Hleft Hright. unfold beq.
  rewrite Bool.andb_true_iff, !forallb_elements. split.
  - intros [Hlr Hrl] key.
    destruct (get key left) as [x|] eqn:El;
      destruct (get key right) as [y|] eqn:Er; cbn.
    + pose proof (Hlr key x (@elements_sound A left key x El)) as Hxy.
      now rewrite Er in Hxy.
    + specialize (Hlr key x (@elements_sound A left key x El)). now rewrite Er in Hlr.
    + specialize (Hrl key y (@elements_sound A right key y Er)). now rewrite El in Hrl.
    + exact I.
  - intros Hpoint. split.
    + intros key value Hin.
      pose proof (@elements_complete_wf A left Hleft key value Hin) as El.
      specialize (Hpoint key). rewrite El in Hpoint.
      destruct (get key right); cbn in Hpoint |- *; [exact Hpoint|contradiction].
    + intros key value Hin.
      pose proof (@elements_complete_wf A right Hright key value Hin) as Er.
      specialize (Hpoint key). rewrite Er in Hpoint.
      destruct (get key left); cbn in Hpoint |- *; [exact Hpoint|contradiction].
Qed.

Corollary beq_extensional_wf:
  forall (A : Type) (eqA : A -> A -> bool) (left right : t A),
    (forall x y, eqA x y = true <-> x = y) ->
    wf left -> wf right ->
    beq eqA left right = true <-> equiv left right.
Proof.
  intros A eqA left right Heq Hleft Hright.
  rewrite (@beq_correct_wf A eqA left right Hleft Hright).
  unfold equiv. split.
  - intros Hpoint key. specialize (Hpoint key).
    destruct (get key left) as [left_value|] eqn:Eleft;
      destruct (get key right) as [right_value|] eqn:Eright;
      cbn in Hpoint.
    + apply (proj1 (Heq left_value right_value)) in Hpoint. now subst.
    + contradiction.
    + contradiction.
    + reflexivity.
  - intros Hlookup key. specialize (Hlookup key).
    destruct (get key left) as [left_value|] eqn:Eleft;
      destruct (get key right) as [right_value|] eqn:Eright;
      cbn in Hlookup |- *; try congruence; try exact I.
    apply (proj2 (Heq left_value right_value)). congruence.
Qed.

Lemma all_keys_none:
  forall (A : Type) (P : positive -> Prop) (m : t A) key,
    all_keys P m -> ~ P key -> get key m = None.
Proof.
  intros A P m key Hall Hnot.
  destruct (get key m) eqn:E; auto.
  exfalso. apply Hnot. now apply (Hall key a).
Qed.

Lemma wf_empty_or_nonempty:
  forall (A : Type) (m : t A), wf m -> m = Empty \/ nonempty m.
Proof.
  intros A m Hwf.
  induction Hwf as
      [|k v|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har].
  - now left.
  - right. exists k, v. simpl. now rewrite Pos.eqb_refl.
  - right. destruct Hnl as [k [v E]]. exists k, v. cbn.
    pose proof (Hall _ _ E) as [P Z]. now rewrite P, Z.
Qed.

Lemma representative_none_wf:
  forall (A : Type) (m : t A), wf m ->
    representative m = None -> m = Empty.
Proof.
  intros A m Hwf. induction Hwf as
      [|k v|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har]; intro H.
  - reflexivity.
  - cbn in H. discriminate.
  - cbn in H. destruct (representative l) eqn:El; try discriminate.
    assert (l = Empty) by (apply IHl; reflexivity).
    subst l. destruct Hnl as [key [value E]]. discriminate.
Qed.

Lemma representative_get_wf:
  forall (A : Type) (m : t A), wf m ->
  forall key, representative m = Some key ->
    exists value, get key m = Some value.
Proof.
  intros A m Hwf.
  induction Hwf as
      [|k v|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har];
    intros key Hrep; cbn in Hrep.
  - discriminate.
  - inversion Hrep; subst. exists v. cbn. now rewrite Pos.eqb_refl.
  - destruct (representative l) eqn:El.
    + inversion Hrep; subst key.
      destruct (IHl _ eq_refl) as [value E].
      exists value. cbn. pose proof (Hall _ _ E) as [P Z]. now rewrite P, Z.
    + apply (representative_none_wf Hwl) in El. subst l.
      destruct Hnl as [witness [found E]]. discriminate.
Qed.

Lemma all_keys_leaf:
  forall (A : Type) (P : positive -> Prop) key (value : A),
    P key -> all_keys P (Leaf key value).
Proof.
  intros A P key value HP query found Hget. cbn in Hget.
  destruct (Pos.eqb query key) eqn:E; try discriminate.
  inversion Hget; subst. apply Pos.eqb_eq in E. now subst.
Qed.

(** The semantic precondition below is precisely what [join] needs: every
    existing binding sees the fresh key's first differing bit at the same
    position as the chosen representative. *)
Lemma join_leaf_correct:
  forall (A : Type) fresh (value : A) (m : t A) rep,
    wf m -> representative m = Some rep -> fresh <> rep ->
    get fresh m = None ->
    (forall key old,
      get key m = Some old ->
      highest_differing_bit fresh key = highest_differing_bit fresh rep) ->
    wf (join (Leaf fresh value) m) /\
    forall key,
      get key (join (Leaf fresh value) m) =
      if Pos.eqb key fresh then Some value else get key m.
Proof.
  intros A fresh value m rep Hwf Hrep Hneq Hmissing Hhighest.
  pose proof (representative_get_wf Hwf Hrep) as [rep_value Hgetrep].
  unfold join. cbn. rewrite Hrep.
  destruct (Pos.eqb fresh rep) eqn:E; [apply Pos.eqb_eq in E; contradiction|].
  set (mask := highest_differing_bit fresh rep).
  assert (Hfresh_nonempty : nonempty (Leaf fresh value)).
  { exists fresh, value. cbn. now rewrite Pos.eqb_refl. }
  assert (Hfresh_prefix : all_keys
      (fun k => matches_prefix k (prefix fresh mask) mask = true /\
                zero_bit k mask = zero_bit fresh mask)
      (Leaf fresh value)).
  { apply all_keys_leaf. split; [apply matches_prefix_refl|reflexivity]. }
  assert (Hold_prefix : all_keys
      (fun k => matches_prefix k (prefix fresh mask) mask = true /\
                zero_bit k mask = negb (zero_bit fresh mask)) m).
  { intros key old Hget.
    assert (Hfk : fresh <> key).
    { intro K. subst key. congruence. }
    specialize (Hhighest key old Hget). split.
    - unfold matches_prefix. apply N.eqb_eq.
      unfold mask.
      rewrite <- Hhighest. symmetry. now apply highest_prefix_agrees.
    - unfold mask. rewrite <- Hhighest. now apply highest_zero_bit_opposite. }
  destruct (zero_bit fresh mask) eqn:Z.
  - split.
    + eapply wf_branch.
      * constructor.
      * exact Hwf.
      * exact Hfresh_nonempty.
      * exists rep, rep_value. exact Hgetrep.
      * eapply all_keys_leaf. split; [apply matches_prefix_refl|exact Z].
      * intros key old Hget. specialize (Hold_prefix _ _ Hget) as [P B].
        split; [exact P|]. exact B.
    + intro key. destruct (Pos.eqb key fresh) eqn:K.
      * apply Pos.eqb_eq in K. subst. cbn [get].
        rewrite matches_prefix_refl, Z. cbn. now rewrite Pos.eqb_refl.
      * cbn [get]. destruct (matches_prefix key (prefix fresh mask) mask) eqn:P.
        -- destruct (zero_bit key mask) eqn:B; cbn [get]; rewrite ?K.
           ++ symmetry. eapply all_keys_none; [exact Hold_prefix|].
              cbn. intuition congruence.
           ++ reflexivity.
        -- symmetry. eapply all_keys_none; [exact Hold_prefix|].
           cbn. intuition congruence.
  - split.
    + eapply wf_branch.
      * exact Hwf.
      * constructor.
      * exists rep, rep_value. exact Hgetrep.
      * exact Hfresh_nonempty.
      * intros key old Hget. specialize (Hold_prefix _ _ Hget) as [P B].
        split; [exact P|]. exact B.
      * eapply all_keys_leaf. split; [apply matches_prefix_refl|exact Z].
    + intro key. destruct (Pos.eqb key fresh) eqn:K.
      * apply Pos.eqb_eq in K. subst. cbn [get].
        rewrite matches_prefix_refl, Z. cbn. now rewrite Pos.eqb_refl.
      * cbn [get]. destruct (matches_prefix key (prefix fresh mask) mask) eqn:P.
        -- destruct (zero_bit key mask) eqn:B; cbn [get]; rewrite ?K.
           ++ reflexivity.
           ++ symmetry. eapply all_keys_none; [exact Hold_prefix|].
              cbn. intuition congruence.
        -- symmetry. eapply all_keys_none; [exact Hold_prefix|].
           cbn. intuition congruence.
Qed.

Lemma join_compatible_correct:
  forall (A : Type) (left right : t A) lrep rrep,
    wf left -> wf right ->
    representative left = Some lrep -> representative right = Some rrep ->
    lrep <> rrep ->
    let mask := highest_differing_bit lrep rrep in
    all_keys
      (fun k => matches_prefix k (prefix lrep mask) mask = true /\
                zero_bit k mask = zero_bit lrep mask) left ->
    all_keys
      (fun k => matches_prefix k (prefix lrep mask) mask = true /\
                zero_bit k mask = negb (zero_bit lrep mask)) right ->
    wf (join left right) /\
    forall key,
      get key (join left right) =
      match get key left with Some value => Some value | None => get key right end.
Proof.
  intros A left right lrep rrep Hwl Hwr Hlrep Hrrep Hneq mask Hall Har.
  pose proof (representative_get_wf Hwl Hlrep) as [lv Hlv].
  pose proof (representative_get_wf Hwr Hrrep) as [rv Hrv].
  unfold join. rewrite Hlrep, Hrrep.
  destruct (Pos.eqb lrep rrep) eqn:E; [apply Pos.eqb_eq in E; contradiction|].
  change (highest_differing_bit lrep rrep) with mask.
  destruct (zero_bit lrep mask) eqn:Z.
  - split.
    + eapply wf_branch.
      * exact Hwl.
      * exact Hwr.
      * exists lrep, lv. exact Hlv.
      * exists rrep, rv. exact Hrv.
      * intros key value Hget. specialize (Hall _ _ Hget) as [P B].
        split; [exact P|]. exact B.
      * intros key value Hget. specialize (Har _ _ Hget) as [P B].
        split; [exact P|]. exact B.
    + intro key. cbn [get].
      destruct (matches_prefix key (prefix lrep mask) mask) eqn:P.
      * destruct (zero_bit key mask) eqn:B.
        -- destruct (get key left) eqn:L; auto.
           assert (get key right = None) as R.
           { eapply all_keys_none; [exact Har|]. cbn. intuition congruence. }
           now rewrite R.
        -- assert (get key left = None) as L.
           { eapply all_keys_none; [exact Hall|]. cbn. intuition congruence. }
           now rewrite L.
      * assert (get key left = None) as L.
        { eapply all_keys_none; [exact Hall|]. cbn. intuition congruence. }
        assert (get key right = None) as R.
        { eapply all_keys_none; [exact Har|]. cbn. intuition congruence. }
        now rewrite L, R.
  - split.
    + eapply wf_branch.
      * exact Hwr.
      * exact Hwl.
      * exists rrep, rv. exact Hrv.
      * exists lrep, lv. exact Hlv.
      * intros key value Hget. specialize (Har _ _ Hget) as [P B].
        split; [exact P|]. exact B.
      * intros key value Hget. specialize (Hall _ _ Hget) as [P B].
        split; [exact P|]. exact B.
    + intro key. cbn [get].
      destruct (matches_prefix key (prefix lrep mask) mask) eqn:P.
      * destruct (zero_bit key mask) eqn:B.
        -- assert (get key left = None) as L.
           { eapply all_keys_none; [exact Hall|]. cbn. intuition congruence. }
           now rewrite L.
        -- destruct (get key left) eqn:L; auto.
           assert (get key right = None) as R.
           { eapply all_keys_none; [exact Har|]. cbn. intuition congruence. }
           now rewrite R.
      * assert (get key left = None) as L.
        { eapply all_keys_none; [exact Hall|]. cbn. intuition congruence. }
        assert (get key right = None) as R.
        { eapply all_keys_none; [exact Har|]. cbn. intuition congruence. }
        now rewrite L, R.
Qed.

Theorem set_correct_wf:
  forall (A : Type) fresh (value : A) (m : t A), wf m ->
    wf (set fresh value m) /\
    forall key,
      get key (set fresh value m) =
      if Pos.eqb key fresh then Some value else get key m.
Proof.
  intros A fresh value m Hwf.
  induction Hwf as
      [|stored old|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har].
  - split; [constructor|]. intro key. cbn.
    destruct (Pos.eqb key fresh); reflexivity.
  - cbn [set]. destruct (Pos.eqb fresh stored) eqn:FS.
    + split; [constructor|]. intro key. cbn [get].
      apply Pos.eqb_eq in FS. subst stored.
      destruct (Pos.eqb key fresh); reflexivity.
    + apply join_leaf_correct with (rep := stored).
      * constructor.
      * reflexivity.
      * now apply Pos.eqb_neq.
      * cbn [get]. now rewrite FS.
      * intros key found Hget. cbn [get] in Hget.
        destruct (Pos.eqb key stored) eqn:KS; try discriminate.
        apply Pos.eqb_eq in KS. now subst key.
  - destruct IHl as [Hwsl Hgetl]. destruct IHr as [Hwsr Hgetr].
    destruct (matches_prefix fresh p mask) eqn:FP.
    + destruct (zero_bit fresh mask) eqn:FZ.
      * split.
        -- cbn [set]. rewrite FP, FZ. eapply wf_branch.
           ++ exact Hwsl.
           ++ exact Hwr.
           ++ exists fresh, value. apply get_set_same.
           ++ exact Hnr.
           ++ intros key found Hget.
              specialize (Hgetl key). destruct (Pos.eqb key fresh) eqn:KF.
              ** apply Pos.eqb_eq in KF. subst key. split; assumption.
              ** apply Hall with found. congruence.
           ++ exact Har.
        -- intro key. cbn [set]. rewrite FP, FZ. cbn [get].
           destruct (Pos.eqb key fresh) eqn:KF.
           ++ apply Pos.eqb_eq in KF. subst key.
              rewrite FP, FZ, get_set_same. reflexivity.
           ++ destruct (matches_prefix key p mask) eqn:KP;
                [destruct (zero_bit key mask) eqn:KZ|]; cbn;
                rewrite ?KP, ?KZ; auto.
              rewrite Hgetl, KF. reflexivity.
      * split.
        -- cbn [set]. rewrite FP, FZ. eapply wf_branch.
           ++ exact Hwl.
           ++ exact Hwsr.
           ++ exact Hnl.
           ++ exists fresh, value. apply get_set_same.
           ++ exact Hall.
           ++ intros key found Hget.
              specialize (Hgetr key). destruct (Pos.eqb key fresh) eqn:KF.
              ** apply Pos.eqb_eq in KF. subst key. split; assumption.
              ** apply Har with found. congruence.
        -- intro key. cbn [set]. rewrite FP, FZ. cbn [get].
           destruct (Pos.eqb key fresh) eqn:KF.
           ++ apply Pos.eqb_eq in KF. subst key.
              rewrite FP, FZ, get_set_same. reflexivity.
           ++ destruct (matches_prefix key p mask) eqn:KP;
                [destruct (zero_bit key mask) eqn:KZ|]; cbn;
                rewrite ?KP, ?KZ; auto.
              rewrite Hgetr, KF. reflexivity.
    + assert (Hfresh_missing : get fresh (Branch p mask l r) = None).
      { cbn [get]. now rewrite FP. }
      destruct (representative l) as [rep|] eqn:Rl.
      * assert (Hrep_binding : exists found, get rep l = Some found).
        { now apply representative_get_wf. }
        destruct Hrep_binding as [rep_value Hgetrep].
        pose proof (Hall _ _ Hgetrep) as [Hrep_prefix Hrep_bit].
        assert (Hfresh_rep : fresh <> rep).
        { intro E. subst rep. rewrite FP in Hrep_prefix. discriminate. }
        cbn [set]. rewrite FP.
        apply join_leaf_correct with (rep := rep).
        -- now apply wf_branch.
        -- cbn [representative]. now rewrite Rl.
        -- exact Hfresh_rep.
        -- exact Hfresh_missing.
        -- intros key found Hget.
           cbn [get] in Hget.
           destruct (matches_prefix key p mask) eqn:KP; try discriminate.
           assert (Hkey_prefix : prefix key mask = p).
           { unfold matches_prefix in KP. now apply N.eqb_eq in KP. }
           assert (Hrep_prefix' : prefix rep mask = p).
           { unfold matches_prefix in Hrep_prefix.
             now apply N.eqb_eq in Hrep_prefix. }
           assert (Hfresh_prefix : prefix fresh mask <> prefix rep mask).
           { rewrite Hrep_prefix'. unfold matches_prefix in FP.
             now apply N.eqb_neq in FP. }
           eapply highest_differing_same_prefix with (j := key) (k := rep).
           ++ now rewrite Hrep_prefix', Hkey_prefix.
           ++ rewrite Hkey_prefix, <- Hrep_prefix'. exact Hfresh_prefix.
      * apply (representative_none_wf Hwl) in Rl. subst l.
        destruct Hnl as [key [found E]]. discriminate.
Qed.

Corollary get_set_other_wf:
  forall (A : Type) i j (value : A) (m : t A),
    wf m -> i <> j -> get i (set j value m) = get i m.
Proof.
  intros A i j value m Hwf Hneq.
  pose proof (proj2 (set_correct_wf j value Hwf) i) as H.
  apply Pos.eqb_neq in Hneq. now rewrite Hneq in H.
Qed.

Corollary set_wf:
  forall (A : Type) key (value : A) (m : t A),
    wf m -> wf (set key value m).
Proof. intros. now apply set_correct_wf. Qed.

Lemma branch_wf:
  forall (A : Type) p mask (l r : t A),
    wf l -> wf r ->
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = true) l ->
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = false) r ->
    wf (branch p mask l r).
Proof.
  intros A p mask l r Hwl Hwr Hall Har.
  destruct (wf_empty_or_nonempty Hwl) as [Hl|Hnl];
    destruct (wf_empty_or_nonempty Hwr) as [Hr|Hnr].
  - subst. cbn [branch]. constructor.
  - subst l. cbn [branch]. exact Hwr.
  - subst r. unfold branch. destruct l; exact Hwl.
  - assert (Hle : l <> Empty).
    { intro E. subst. destruct Hnl as [k [v H]]. discriminate. }
    assert (Hre : r <> Empty).
    { intro E. subst. destruct Hnr as [k [v H]]. discriminate. }
    unfold branch. destruct l; try contradiction; destruct r; try contradiction;
      constructor; auto.
Qed.

Lemma get_branch:
  forall (A : Type) p mask (l r : t A),
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = true) l ->
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = false) r ->
    forall key,
      get key (branch p mask l r) =
      if matches_prefix key p mask then
        if zero_bit key mask then get key l else get key r
      else None.
Proof.
  intros A p mask l r Hall Har key.
  destruct l as [|lk lv|lp lm ll lr].
  - unfold branch. destruct (matches_prefix key p mask) eqn:P;
      destruct (zero_bit key mask) eqn:Z; try reflexivity;
      fold (@get A); apply all_keys_none with
        (P := fun k => matches_prefix k p mask = true /\ zero_bit k mask = false);
      auto; rewrite P, Z; intuition discriminate.
  - destruct r as [|rk rv|rp rm rl rr]; unfold branch; try reflexivity;
      destruct (matches_prefix key p mask) eqn:P;
      destruct (zero_bit key mask) eqn:Z; try reflexivity;
      fold (@get A); apply all_keys_none with
        (P := fun k => matches_prefix k p mask = true /\ zero_bit k mask = true);
      auto; rewrite P, Z; intuition discriminate.
  - destruct r as [|rk rv|rp rm rl rr]; unfold branch; try reflexivity;
      destruct (matches_prefix key p mask) eqn:P;
      destruct (zero_bit key mask) eqn:Z; try reflexivity;
      fold (@get A); apply all_keys_none with
        (P := fun k => matches_prefix k p mask = true /\ zero_bit k mask = true);
      auto; rewrite P, Z; intuition discriminate.
Qed.

Theorem map_filter_correct_wf:
  forall (A B : Type) (f : positive -> A -> option B) (m : t A), wf m ->
    wf (map_filter f m) /\
    forall key,
      get key (map_filter f m) =
      match get key m with
      | Some value => f key value
      | None => None
      end.
Proof.
  intros A B f m Hwf.
  induction Hwf as
      [|stored value|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har].
  - split; [constructor|reflexivity].
  - cbn [map_filter]. destruct (f stored value) eqn:F.
    + split; [constructor|]. intro key. cbn [get].
      destruct (Pos.eqb key stored) eqn:K; auto.
      apply Pos.eqb_eq in K. now subst key.
    + split; [constructor|]. intro key. cbn [get].
      destruct (Pos.eqb key stored) eqn:K; auto.
      apply Pos.eqb_eq in K. now subst key.
  - destruct IHl as [Hwml Hgetl]. destruct IHr as [Hwmr Hgetr].
    assert (Hall' : all_keys
        (fun k => matches_prefix k p mask = true /\ zero_bit k mask = true)
        (map_filter f l)).
    { intros key found Hget. specialize (Hgetl key).
      destruct (get key l) as [old|] eqn:E; cbn in Hgetl; try congruence.
      apply Hall with old. exact E. }
    assert (Har' : all_keys
        (fun k => matches_prefix k p mask = true /\ zero_bit k mask = false)
        (map_filter f r)).
    { intros key found Hget. specialize (Hgetr key).
      destruct (get key r) as [old|] eqn:E; cbn in Hgetr; try congruence.
      apply Har with old. exact E. }
    split.
    + cbn [map_filter]. now apply branch_wf.
    + intro key. cbn [map_filter]. rewrite get_branch by assumption.
      cbn [get]. destruct (matches_prefix key p mask) eqn:P; auto.
      destruct (zero_bit key mask) eqn:Z; [apply Hgetl|apply Hgetr].
Qed.

Corollary map_left_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (m : t A), wf m ->
    wf (map_left f m) /\
    forall key,
      get key (map_left f m) =
      match get key m with Some value => f (Some value) None | None => None end.
Proof. intros. apply map_filter_correct_wf. assumption. Qed.

Corollary map_right_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (m : t B), wf m ->
    wf (map_right f m) /\
    forall key,
      get key (map_right f m) =
      match get key m with Some value => f None (Some value) | None => None end.
Proof. intros. apply map_filter_correct_wf. assumption. Qed.

Lemma all_keys_map_left:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (P : positive -> Prop) (m : t A), wf m ->
    all_keys P m -> all_keys P (map_left f m).
Proof.
  intros A B C f P m Hwf Hall key found Hget.
  pose proof (proj2 (map_left_correct_wf f Hwf) key) as Hmap.
  destruct (get key m) as [old|] eqn:E; cbn in Hmap; try congruence.
  now apply (Hall key old).
Qed.

Lemma all_keys_map_right:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (P : positive -> Prop) (m : t B), wf m ->
    all_keys P m -> all_keys P (map_right f m).
Proof.
  intros A B C f P m Hwf Hall key found Hget.
  pose proof (proj2 (map_right_correct_wf f Hwf) key) as Hmap.
  destruct (get key m) as [old|] eqn:E; cbn in Hmap; try congruence.
  now apply (Hall key old).
Qed.

Lemma map_left_binding_source:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (m : t A), wf m -> forall key found,
    get key (map_left f m) = Some found ->
    exists old, get key m = Some old.
Proof.
  intros A B C f m Hwf key found Hget.
  pose proof (proj2 (map_left_correct_wf f Hwf) key) as Hspec.
  destruct (get key m) as [old|] eqn:E.
  - now exists old.
  - cbn in Hspec. congruence.
Qed.

Lemma map_right_binding_source:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (m : t B), wf m -> forall key found,
    get key (map_right f m) = Some found ->
    exists old, get key m = Some old.
Proof.
  intros A B C f m Hwf key found Hget.
  pose proof (proj2 (map_right_correct_wf f Hwf) key) as Hspec.
  destruct (get key m) as [old|] eqn:E.
  - now exists old.
  - cbn in Hspec. congruence.
Qed.

Lemma branch_all_prefix:
  forall (A : Type) p mask (l r : t A),
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = true) l ->
    all_keys (fun k => matches_prefix k p mask = true /\ zero_bit k mask = false) r ->
    all_keys (fun k => matches_prefix k p mask = true) (Branch p mask l r).
Proof.
  intros A p mask l r Hall Har key found Hget. cbn [get] in Hget.
  destruct (matches_prefix key p mask) eqn:P; try discriminate. reflexivity.
Qed.

Lemma all_keys_uniform_above:
  forall (A : Type) (m : t A) p root_mask rep outer_mask,
    all_keys (fun k => matches_prefix k p root_mask = true) m ->
    (root_mask < outer_mask)%N ->
    get rep m <> None ->
    all_keys
      (fun k => matches_prefix k (prefix rep outer_mask) outer_mask = true /\
                zero_bit k outer_mask = zero_bit rep outer_mask) m.
Proof.
  intros A m p root_mask rep outer_mask Hall Hm Hrep key found Hget.
  destruct (get rep m) as [rep_value|] eqn:Erep; [|contradiction].
  specialize (Hall key found Hget) as Hkey.
  specialize (Hall rep rep_value Erep) as Hr.
  unfold matches_prefix in Hkey, Hr. apply N.eqb_eq in Hkey.
  apply N.eqb_eq in Hr.
  assert (Hprefix : prefix key root_mask = prefix rep root_mask) by congruence.
  split.
  - unfold matches_prefix. apply N.eqb_eq.
    eapply prefix_mono; eauto. lia.
  - eapply same_prefix_zero_bit_above; eauto.
Qed.

Lemma all_keys_of_combine_lookup:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (left : t A) (right : t B) (out : t C) (P : positive -> Prop),
    f None None = None ->
    (forall key, get key out = f (get key left) (get key right)) ->
    all_keys P left -> all_keys P right -> all_keys P out.
Proof.
  intros A B C f left right out P Hnone Hget Hall Har key found E.
  specialize (Hget key). destruct (get key left) as [lv|] eqn:L;
    destruct (get key right) as [rv|] eqn:R.
  - now apply (Hall key lv).
  - now apply (Hall key lv).
  - now apply (Har key rv).
  - rewrite Hnone in Hget. congruence.
Qed.

Lemma join_disjoint_correct:
  forall (A : Type) (left right : t A) lp lm rp rm,
    wf left -> wf right ->
    all_keys (fun k => matches_prefix k lp lm = true) left ->
    all_keys (fun k => matches_prefix k rp rm = true) right ->
    (forall lk lv rk rv,
      get lk left = Some lv -> get rk right = Some rv ->
      (lm < highest_differing_bit lk rk)%N /\
      (rm < highest_differing_bit lk rk)%N) ->
    wf (join left right) /\
    forall key,
      get key (join left right) =
      match get key left with Some value => Some value | None => get key right end.
Proof.
  intros A left right lp lm rp rm Hwl Hwr Hall Har Hd.
  destruct (wf_empty_or_nonempty Hwl) as [El|Hnl];
    destruct (wf_empty_or_nonempty Hwr) as [Er|Hnr].
  - subst. split; [constructor|reflexivity].
  - subst left. cbn [join representative]. split; [exact Hwr|reflexivity].
  - subst right. unfold join. cbn. destruct (representative left) eqn:R; cbn.
    + split; [exact Hwl|]. intro key. now destruct (get key left).
    + apply (representative_none_wf Hwl) in R. subst left.
      destruct Hnl as [key [value E]]. discriminate.
  - destruct (representative left) as [lrep|] eqn:Rl.
    2:{ apply (representative_none_wf Hwl) in Rl. subst left.
        destruct Hnl as [key [value E]]. discriminate. }
    destruct (representative right) as [rrep|] eqn:Rr.
    2:{ apply (representative_none_wf Hwr) in Rr. subst right.
        destruct Hnr as [key [value E]]. discriminate. }
    destruct (representative_get_wf Hwl Rl) as [lv Hlv].
    destruct (representative_get_wf Hwr Rr) as [rv Hrv].
    specialize (Hd lrep lv rrep rv Hlv Hrv) as [Hlm Hrm].
    assert (Hneq : lrep <> rrep).
    { intro E. subst rrep. unfold highest_differing_bit in Hlm.
      rewrite N.lxor_nilpotent in Hlm. cbn in Hlm. lia. }
    set (mask := highest_differing_bit lrep rrep).
    assert (Hlnot : get lrep left <> None) by (rewrite Hlv; discriminate).
    assert (Hrnot : get rrep right <> None) by (rewrite Hrv; discriminate).
    pose proof (@all_keys_uniform_above A left lp lm lrep mask
      Hall Hlm Hlnot) as Hleft_uniform.
    pose proof (@all_keys_uniform_above A right rp rm rrep mask
      Har Hrm Hrnot) as Hright_own.
    assert (Hright_uniform : all_keys
        (fun k => matches_prefix k (prefix lrep mask) mask = true /\
                  zero_bit k mask = negb (zero_bit lrep mask)) right).
    { intros key value Hget. specialize (Hright_own _ _ Hget) as [P B].
      split.
      - unfold matches_prefix in P |- *. apply N.eqb_eq in P. apply N.eqb_eq.
        rewrite P. unfold mask. symmetry. now apply highest_prefix_agrees.
      - rewrite B. unfold mask. now apply highest_zero_bit_opposite. }
    eapply join_compatible_correct; eauto.
Qed.

Lemma all_keys_after_remove:
  forall (A : Type) (P : positive -> Prop) (old fresh : t A) removed,
    (forall key,
      get key fresh = if Pos.eqb key removed then None else get key old) ->
    all_keys P old -> all_keys P fresh.
Proof.
  intros A P old fresh removed Hget Hall key value E.
  specialize (Hget key). destruct (Pos.eqb key removed) eqn:K.
  - congruence.
  - apply Hall with value. congruence.
Qed.

Lemma nonempty_not_empty:
  forall (A : Type) (m : t A), nonempty m -> m <> Empty.
Proof.
  intros A m [key [value Hget]] ->. discriminate.
Qed.

Lemma branch_unchanged:
  forall (A : Type) p mask (l r : t A),
    nonempty l -> nonempty r -> branch p mask l r = Branch p mask l r.
Proof.
  intros A p mask l r Hnl Hnr. unfold branch.
  destruct l.
  - exfalso. now apply (nonempty_not_empty Hnl).
  - destruct r.
    + exfalso. now apply (nonempty_not_empty Hnr).
    + reflexivity.
    + reflexivity.
  - destruct r.
    + exfalso. now apply (nonempty_not_empty Hnr).
    + reflexivity.
    + reflexivity.
Qed.

Lemma remove_reference_changed_wf:
  forall (A : Type) removed (m : t A), wf m ->
    remove_reference removed m =
      match remove_changed removed m with
      | None => m
      | Some changed => changed
      end.
Proof.
  intros A removed m Hwf.
  induction Hwf as
      [|stored value|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har].
  - reflexivity.
  - cbn [remove_reference remove_changed].
    now destruct (Pos.eqb removed stored).
  - cbn [remove_reference remove_changed].
    destruct (matches_prefix removed p mask) eqn:RP; [|reflexivity].
    destruct (zero_bit removed mask) eqn:RZ.
    + destruct (remove_changed removed l) as [changed|] eqn:E; cbn.
      * now rewrite IHl.
      * rewrite IHl. now apply branch_unchanged.
    + destruct (remove_changed removed r) as [changed|] eqn:E; cbn.
      * now rewrite IHr.
      * rewrite IHr. now apply branch_unchanged.
Qed.

Lemma remove_eq_reference:
  forall (A : Type) removed (m : t A), wf m ->
    remove removed m = remove_reference removed m.
Proof.
  intros A removed m Hwf. unfold remove.
  symmetry. now apply remove_reference_changed_wf.
Qed.

Lemma remove_changed_none_of_get_none:
  forall (A : Type) removed (m : t A),
    get removed m = None -> remove_changed removed m = None.
Proof.
  intros A removed m.
  induction m as [|stored value|p mask l IHl r IHr]; intro Hget.
  - reflexivity.
  - cbn [get remove_changed] in *.
    now destruct (Pos.eqb removed stored).
  - cbn [get remove_changed] in *.
    destruct (matches_prefix removed p mask); [|reflexivity].
    destruct (zero_bit removed mask); [now rewrite IHl|now rewrite IHr].
Qed.

Theorem remove_absent_identity:
  forall (A : Type) removed (m : t A),
    get removed m = None -> remove removed m = m.
Proof.
  intros A removed m Hget. unfold remove.
  now rewrite (remove_changed_none_of_get_none removed m Hget).
Qed.

Theorem remove_reference_correct_wf:
  forall (A : Type) removed (m : t A), wf m ->
    wf (remove_reference removed m) /\
    forall key,
      get key (remove_reference removed m) =
      if Pos.eqb key removed then None else get key m.
Proof.
  intros A removed m Hwf.
  induction Hwf as
      [|stored value|p mask l r Hwl IHl Hwr IHr Hnl Hnr Hall Har].
  - split; [constructor|]. intros. cbn. destruct (Pos.eqb key removed); reflexivity.
  - split.
    + cbn [remove_reference]. destruct (Pos.eqb removed stored); constructor.
    + intros key. cbn [remove_reference]. destruct (Pos.eqb removed stored) eqn:RS.
      * apply Pos.eqb_eq in RS. subst stored. cbn [get].
        destruct (Pos.eqb key removed) eqn:KR; auto.
      * cbn [get].
        destruct (Pos.eqb key removed) eqn:KR; auto.
        apply Pos.eqb_eq in KR. subst key. now rewrite RS.
  - destruct IHl as [Hwrl Hgetl]. destruct IHr as [Hwrr Hgetr].
    destruct (matches_prefix removed p mask) eqn:RP.
    + destruct (zero_bit removed mask) eqn:RZ.
      * assert (Hall' : all_keys
          (fun k => matches_prefix k p mask = true /\ zero_bit k mask = true)
          (remove_reference removed l)).
        { eapply all_keys_after_remove; eauto. }
        split.
        { cbn [remove_reference]. rewrite RP, RZ. now apply branch_wf. }
        intros key. cbn [remove_reference]. rewrite RP, RZ.
        rewrite get_branch by assumption.
        cbn [get].
        destruct (Pos.eqb key removed) eqn:KR.
        { apply Pos.eqb_eq in KR. subst key. now rewrite RP, RZ, Hgetl, Pos.eqb_refl. }
        destruct (matches_prefix key p mask) eqn:KP; [destruct (zero_bit key mask) eqn:KZ|];
          cbn; rewrite ?KP, ?KZ; auto.
        rewrite Hgetl, KR. reflexivity.
      * assert (Har' : all_keys
          (fun k => matches_prefix k p mask = true /\ zero_bit k mask = false)
          (remove_reference removed r)).
        { eapply all_keys_after_remove; eauto. }
        split.
        { cbn [remove_reference]. rewrite RP, RZ. now apply branch_wf. }
        intros key. cbn [remove_reference]. rewrite RP, RZ.
        rewrite get_branch by assumption.
        cbn [get].
        destruct (Pos.eqb key removed) eqn:KR.
        { apply Pos.eqb_eq in KR. subst key. now rewrite RP, RZ, Hgetr, Pos.eqb_refl. }
        destruct (matches_prefix key p mask) eqn:KP; [destruct (zero_bit key mask) eqn:KZ|];
          cbn; rewrite ?KP, ?KZ; auto.
        rewrite Hgetr, KR. reflexivity.
    + split; [cbn [remove_reference]; rewrite RP; constructor; assumption|].
      intros key. cbn [remove_reference]. rewrite RP.
      destruct (Pos.eqb key removed) eqn:KR; auto.
      apply Pos.eqb_eq in KR. subst key. cbn [get]. now rewrite RP.
Qed.

Theorem remove_correct_wf:
  forall (A : Type) removed (m : t A), wf m ->
    wf (remove removed m) /\
    forall key,
      get key (remove removed m) =
      if Pos.eqb key removed then None else get key m.
Proof.
  intros A removed m Hwf.
  rewrite remove_eq_reference by exact Hwf.
  now apply remove_reference_correct_wf.
Qed.

Lemma replace_binding_correct_wf:
  forall (A : Type) key (replacement : option A) (m : t A), wf m ->
    wf (replace_binding key replacement m) /\
    forall query,
      get query (replace_binding key replacement m) =
      if Pos.eqb query key then replacement else get query m.
Proof.
  intros A key [value|] m Hwf; cbn [replace_binding].
  - exact (set_correct_wf key value Hwf).
  - exact (remove_correct_wf key Hwf).
Qed.

Theorem combine_leaf_left_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      key value (m : t B),
    f None None = None -> wf m ->
    wf (combine_leaf_left f key value m) /\
    forall query,
      get query (combine_leaf_left f key value m) =
        f (if Pos.eqb query key then Some value else None) (get query m).
Proof.
  intros A B C f key value m Hnone Hwf.
  unfold combine_leaf_left. destruct (get key m) as [old|] eqn:Ekey.
  - destruct (map_filter_correct_wf
      (fun stored right =>
        if Pos.eqb stored key
        then f (Some value) (Some right)
        else f None (Some right)) Hwf) as [Hwmap Hgetmap].
    split; [exact Hwmap|]. intro query. rewrite Hgetmap.
    destruct (get query m) as [found|] eqn:Equery; cbn.
    + destruct (Pos.eqb query key) eqn:Eequal; reflexivity.
    + destruct (Pos.eqb query key) eqn:Eequal.
      * apply Pos.eqb_eq in Eequal. subst query. congruence.
      * symmetry. exact Hnone.
  - destruct (map_right_correct_wf f Hwf) as [Hwmap Hgetmap].
    destruct (replace_binding_correct_wf key (f (Some value) None) Hwmap)
      as [Hwreplace Hgetreplace].
    split; [exact Hwreplace|]. intro query.
    rewrite Hgetreplace, Hgetmap.
    destruct (Pos.eqb query key) eqn:Eequal.
    + apply Pos.eqb_eq in Eequal. subst query. now rewrite Ekey.
    + destruct (get query m); [reflexivity|]. symmetry. exact Hnone.
Qed.

Theorem combine_leaf_right_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (m : t A) key value,
    f None None = None -> wf m ->
    wf (combine_leaf_right f m key value) /\
    forall query,
      get query (combine_leaf_right f m key value) =
        f (get query m) (if Pos.eqb query key then Some value else None).
Proof.
  intros A B C f m key value Hnone Hwf.
  unfold combine_leaf_right. destruct (get key m) as [old|] eqn:Ekey.
  - destruct (map_filter_correct_wf
      (fun stored left =>
        if Pos.eqb stored key
        then f (Some left) (Some value)
        else f (Some left) None) Hwf) as [Hwmap Hgetmap].
    split; [exact Hwmap|]. intro query. rewrite Hgetmap.
    destruct (get query m) as [found|] eqn:Equery; cbn.
    + destruct (Pos.eqb query key) eqn:Eequal; reflexivity.
    + destruct (Pos.eqb query key) eqn:Eequal.
      * apply Pos.eqb_eq in Eequal. subst query. congruence.
      * symmetry. exact Hnone.
  - destruct (map_left_correct_wf f Hwf) as [Hwmap Hgetmap].
    destruct (replace_binding_correct_wf key (f None (Some value)) Hwmap)
      as [Hwreplace Hgetreplace].
    split; [exact Hwreplace|]. intro query.
    rewrite Hgetreplace, Hgetmap.
    destruct (Pos.eqb query key) eqn:Eequal.
    + apply Pos.eqb_eq in Eequal. subst query. now rewrite Ekey.
    + destruct (get query m); [reflexivity|]. symmetry. exact Hnone.
Qed.

(** A conservative fuel predicate: at a branch/branch node it requires enough
    fuel for every recursive shape used by [combine_fuel], independently of
    which prefix/mask comparison is selected at runtime. *)
Fixpoint combine_fuel_sufficient {A B : Type}
    (fuel : nat) (left : t A) (right : t B) : Prop :=
  match fuel with
  | O => False
  | S fuel' =>
      match left, right with
      | Branch _ _ ll lr, Branch _ _ rl rr =>
          combine_fuel_sufficient fuel' ll rl /\
          combine_fuel_sufficient fuel' lr rr /\
          combine_fuel_sufficient fuel' ll right /\
          combine_fuel_sufficient fuel' lr right /\
          combine_fuel_sufficient fuel' left rl /\
          combine_fuel_sufficient fuel' left rr
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
  destruct left as [|lk lv|lp lm ll lr];
    destruct right as [|rk rv|rp rm rl rr]; cbn in *; auto.
  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  repeat split.
  - exact (IH ll rl H1).
  - exact (IH lr rr H2).
  - exact (IH ll (Branch rp rm rl rr) H3).
  - exact (IH lr (Branch rp rm rl rr) H4).
  - exact (IH (Branch lp lm ll lr) rl H5).
  - exact (IH (Branch lp lm ll lr) rr H6).
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
    intros left right E. destruct left as [|lk lv|lp lm ll lr];
      destruct right as [|rk rv|rp rm rl rr]; cbn; auto.
    repeat split.
    - pose proof (H (size ll + size rl)) as IH.
      assert (Hs := IH ltac:(cbn in E; lia) ll rl eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size lr + S (size rr)) _ _ Hs) as Hm.
      replace total with (S (size ll + size rl) + (size lr + S (size rr))) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size lr + size rr)) as IH.
      assert (Hs := IH ltac:(cbn in E; lia) lr rr eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size ll + S (size rl)) _ _ Hs) as Hm.
      replace total with (S (size lr + size rr) + (size ll + S (size rl))) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size ll + size (Branch rp rm rl rr))) as IH.
      assert (Hlt : size ll + size (Branch rp rm rl rr) < total) by
        (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt ll (Branch rp rm rl rr) eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size lr) _ _ Hs) as Hm.
      replace total with
        (S (size ll + size (Branch rp rm rl rr)) + size lr) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size lr + size (Branch rp rm rl rr))) as IH.
      assert (Hlt : size lr + size (Branch rp rm rl rr) < total) by
        (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt lr (Branch rp rm rl rr) eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size ll) _ _ Hs) as Hm.
      replace total with
        (S (size lr + size (Branch rp rm rl rr)) + size ll) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size (Branch lp lm ll lr) + size rl)) as IH.
      assert (Hlt : size (Branch lp lm ll lr) + size rl < total) by
        (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt (Branch lp lm ll lr) rl eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size rr) _ _ Hs) as Hm.
      replace total with
        (S (size (Branch lp lm ll lr) + size rl) + size rr) by
        (cbn [size] in E |- *; lia). exact Hm.
    - pose proof (H (size (Branch lp lm ll lr) + size rr)) as IH.
      assert (Hlt : size (Branch lp lm ll lr) + size rr < total) by
        (cbn [size] in E |- *; lia).
      assert (Hs := IH Hlt (Branch lp lm ll lr) rr eq_refl).
      pose proof (@combine_fuel_sufficient_monotone A B _
        (size rl) _ _ Hs) as Hm.
      replace total with
        (S (size (Branch lp lm ll lr) + size rr) + size rl) by
        (cbn [size] in E |- *; lia). exact Hm. }
  intros. apply Hstrong with (total := size left + size right). reflexivity.
Qed.

(** Direct structural recursion follows exactly the same branch chosen by the
    fuelled reference whenever the latter is given sufficient fuel. *)
Theorem combine_structural_eq_combine_fuel:
  forall (A B C : Type) fuel
      (f : option A -> option B -> option C) (left : t A) (right : t B),
    combine_fuel_sufficient fuel left right ->
    combine_structural f left right = combine_fuel fuel f left right.
Proof.
  intros A B C fuel. induction fuel as [|fuel IH]; intros f left right Hfuel.
  - cbn in Hfuel. contradiction.
  - destruct left as [|lk lv|lp lm ll lr];
      destruct right as [|rk rv|rp rm rl rr]; cbn in Hfuel |- *; auto.
    destruct Hfuel as [Hll [Hrr [Hlr [Hrright [Hlleft Hlright]]]]].
    cbn [combine_structural, combine_fuel].
    destruct (N.eqb lm rm && N.eqb lp rp)%bool eqn:Eequal; cbn.
    + rewrite (IH f ll rl Hll), (IH f lr rr Hrr). reflexivity.
    + destruct (mask_above lm rm) eqn:Eleft; cbn.
      * destruct (representative (Branch rp rm rl rr)) as [key|] eqn:Erep; cbn.
        -- destruct (matches_prefix key lp lm) eqn:Eprefix; cbn; auto.
           destruct (zero_bit key lm) eqn:Ebit; cbn.
           ++ rewrite (IH f ll (Branch rp rm rl rr) Hlr). reflexivity.
           ++ rewrite (IH f lr (Branch rp rm rl rr) Hrright). reflexivity.
        -- reflexivity.
      * destruct (mask_above rm lm) eqn:Eright; cbn; auto.
        destruct (representative (Branch lp lm ll lr)) as [key|] eqn:Erep; cbn.
        -- destruct (matches_prefix key rp rm) eqn:Eprefix; cbn; auto.
           destruct (zero_bit key rm) eqn:Ebit; cbn.
           ++ rewrite (IH f (Branch lp lm ll lr) rl Hlleft). reflexivity.
           ++ rewrite (IH f (Branch lp lm ll lr) rr Hlright). reflexivity.
        -- reflexivity.
Qed.

Corollary combine_structural_eq_public_combine_fuel:
  forall (A B C : Type)
      (f : option A -> option B -> option C) (left : t A) (right : t B),
    combine_structural f left right =
    combine_fuel (S (size left + size right)) f left right.
Proof.
  intros. apply combine_structural_eq_combine_fuel.
  apply public_combine_fuel_sufficient.
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
  destruct left as [|lk lv|lp lm ll lr];
    destruct right as [|rk rv|rp rm rl rr].
  - cbn [combine_fuel map_right map_filter get].
    split; [constructor|]. intro key. symmetry. exact Hnone.
  - cbn [combine_fuel].
    pose proof (map_right_correct_wf f Hwr) as [Hwm Hget]. split; [exact Hwm|].
    intro key. rewrite Hget.
    destruct (get key (Leaf rk rv)); cbn; [reflexivity|symmetry; exact Hnone].
  - cbn [combine_fuel].
    pose proof (map_right_correct_wf f Hwr) as [Hwm Hget]. split; [exact Hwm|].
    intro key. rewrite Hget.
    destruct (get key (Branch rp rm rl rr)); cbn;
      [reflexivity|symmetry; exact Hnone].
  - cbn [combine_fuel].
    pose proof (map_left_correct_wf f Hwl) as [Hwm Hget]. split; [exact Hwm|].
    intro key. rewrite Hget.
    destruct (get key (Leaf lk lv)); cbn; [reflexivity|symmetry; exact Hnone].
  - cbn [combine_fuel].
    pose proof (map_right_correct_wf f Hwr) as [Hwbase Hbase].
    pose proof (replace_binding_correct_wf lk
      (f (Some lv) (get lk (Leaf rk rv))) Hwbase) as [Hwout Hout].
    split; [exact Hwout|]. intro key. rewrite Hout.
    destruct (Pos.eqb key lk) eqn:K.
    + apply Pos.eqb_eq in K. subst key. cbn [get]. now rewrite Pos.eqb_refl.
    + rewrite Hbase. destruct (get key (Leaf rk rv)); cbn;
        rewrite K; [reflexivity|symmetry; exact Hnone].
  - cbn [combine_fuel].
    pose proof (map_right_correct_wf f Hwr) as [Hwbase Hbase].
    pose proof (replace_binding_correct_wf lk
      (f (Some lv) (get lk (Branch rp rm rl rr))) Hwbase) as [Hwout Hout].
    split; [exact Hwout|]. intro key. rewrite Hout.
    destruct (Pos.eqb key lk) eqn:K.
    + apply Pos.eqb_eq in K. subst key. cbn [get]. now rewrite Pos.eqb_refl.
    + rewrite Hbase. destruct (get key (Branch rp rm rl rr)); cbn;
        rewrite K; [reflexivity|symmetry; exact Hnone].
  - cbn [combine_fuel].
    pose proof (map_left_correct_wf f Hwl) as [Hwm Hget]. split; [exact Hwm|].
    intro key. rewrite Hget.
    destruct (get key (Branch lp lm ll lr)); cbn;
      [reflexivity|symmetry; exact Hnone].
  - cbn [combine_fuel].
    pose proof (map_left_correct_wf f Hwl) as [Hwbase Hbase].
    pose proof (replace_binding_correct_wf rk
      (f (get rk (Branch lp lm ll lr)) (Some rv)) Hwbase) as [Hwout Hout].
    split; [exact Hwout|]. intro key. rewrite Hout.
    destruct (Pos.eqb key rk) eqn:K.
    + apply Pos.eqb_eq in K. subst key. cbn [get]. now rewrite Pos.eqb_refl.
    + rewrite Hbase. destruct (get key (Branch lp lm ll lr)); cbn;
        rewrite K; [reflexivity|symmetry; exact Hnone].
  - cbn in Hfuel. destruct Hfuel as [Hsll [Hsrr [Hslar [Hslrr [Hsalr Hsarr]]]]].
    inversion Hwl as [| |? ? ? ? Hwall Hwarr Hnall Hnalr Hall Har]; subst.
    inversion Hwr as [| |? ? ? ? Hwbrl Hwbrr Hnbrl Hnbrr Hbl Hbr]; subst.
    cbn [combine_fuel].
    destruct (N.eqb lm rm && N.eqb lp rp)%bool eqn:Same.
    + apply Bool.andb_true_iff in Same. destruct Same as [Em Ep].
      apply N.eqb_eq in Em. apply N.eqb_eq in Ep. subst rm rp.
      destruct (IH f ll rl Hnone Hwall Hwbrl Hsll) as [Hwcl Hcl].
      destruct (IH f lr rr Hnone Hwarr Hwbrr Hsrr) as [Hwcr Hcr].
      assert (Houtl : all_keys
          (fun k => matches_prefix k lp lm = true /\ zero_bit k lm = true)
          (combine_fuel fuel f ll rl)).
      { eapply all_keys_of_combine_lookup; eauto. }
      assert (Houtr : all_keys
          (fun k => matches_prefix k lp lm = true /\ zero_bit k lm = false)
          (combine_fuel fuel f lr rr)).
      { eapply all_keys_of_combine_lookup; eauto. }
      split.
      * now apply branch_wf.
      * intro key. rewrite get_branch by assumption. cbn [get].
        destruct (matches_prefix key lp lm) eqn:P.
        -- destruct (zero_bit key lm) eqn:Z; [apply Hcl|apply Hcr].
        -- symmetry. exact Hnone.
    + destruct (mask_above lm rm) eqn:Mab.
      * apply mask_above_spec in Mab.
        destruct (representative rl) as [kb|] eqn:Rb.
        2:{ apply (representative_none_wf Hwbrl) in Rb. subst rl.
            destruct Hnbrl as [key [value E]]. discriminate. }
        assert (Hrepb : representative (Branch rp rm rl rr) = Some kb).
        { cbn [representative]. now rewrite Rb. }
        destruct (representative_get_wf Hwr Hrepb) as [kbv Hgetkb].
        assert (Hbprefix : all_keys (fun k => matches_prefix k rp rm = true)
            (Branch rp rm rl rr)) by (now apply branch_all_prefix).
        assert (Hkbnot : get kb (Branch rp rm rl rr) <> None) by
          (rewrite Hgetkb; discriminate).
        pose proof (@all_keys_uniform_above B (Branch rp rm rl rr)
          rp rm kb lm Hbprefix Mab Hkbnot) as Hbouter0.
        destruct (matches_prefix kb lp lm) eqn:KBmatch.
        -- assert (Hbouter : all_keys
              (fun k => matches_prefix k lp lm = true /\
                        zero_bit k lm = zero_bit kb lm)
              (Branch rp rm rl rr)).
           { intros key value Hget. specialize (Hbouter0 _ _ Hget) as [P Z].
             split; [|exact Z]. unfold matches_prefix in P, KBmatch |- *.
             apply N.eqb_eq in P. apply N.eqb_eq in KBmatch. apply N.eqb_eq.
             congruence. }
           destruct (zero_bit kb lm) eqn:KBzero.
           ++ rewrite Hrepb, KBmatch, KBzero.
              destruct (IH f ll (Branch rp rm rl rr) Hnone Hwall Hwr Hslar)
                as [Hwco Hco].
              destruct (map_left_correct_wf f Hwarr) as [Hwmap Hmap].
              assert (Hcol : all_keys
                  (fun k => matches_prefix k lp lm = true /\ zero_bit k lm = true)
                  (combine_fuel fuel f ll (Branch rp rm rl rr))).
              { eapply all_keys_of_combine_lookup.
                - exact Hnone.
                - exact Hco.
                - exact Hall.
                -
                intros key value Hget. specialize (Hbouter _ _ Hget) as [P Z].
                split; [exact P|]. exact Z. }
              assert (Hmapr : all_keys
                  (fun k => matches_prefix k lp lm = true /\ zero_bit k lm = false)
                  (map_left f lr)).
              { eapply all_keys_map_left; eauto. }
              split.
              ** apply branch_wf; assumption.
              ** intro key. rewrite get_branch by assumption.
                 change
                   ((if matches_prefix key lp lm then
                       if zero_bit key lm
                       then get key (combine_fuel fuel f ll (Branch rp rm rl rr))
                       else get key (map_left f lr)
                     else None) =
                    f (if matches_prefix key lp lm then
                         if zero_bit key lm then get key ll else get key lr
                       else None)
                      (get key (Branch rp rm rl rr))).
                 destruct (matches_prefix key lp lm) eqn:P.
                 --- destruct (zero_bit key lm) eqn:Z.
                     +++ apply Hco.
                     +++ rewrite Hmap.
                         assert (get key (Branch rp rm rl rr) = None) as RB.
                         { eapply all_keys_none; [exact Hbouter|].
                           cbn. intuition congruence. }
                         rewrite RB. destruct (get key lr); cbn;
                           [reflexivity|symmetry; exact Hnone].
                 --- assert (get key (Branch rp rm rl rr) = None) as RB.
                     { eapply all_keys_none; [exact Hbouter|].
                       cbn. intuition congruence. }
                     rewrite RB. symmetry. exact Hnone.
           ++ rewrite Hrepb, KBmatch, KBzero.
              destruct (IH f lr (Branch rp rm rl rr) Hnone Hwarr Hwr Hslrr)
                as [Hwco Hco].
              destruct (map_left_correct_wf f Hwall) as [Hwmap Hmap].
              assert (Hcor : all_keys
                  (fun k => matches_prefix k lp lm = true /\ zero_bit k lm = false)
                  (combine_fuel fuel f lr (Branch rp rm rl rr))).
              { eapply all_keys_of_combine_lookup.
                - exact Hnone.
                - exact Hco.
                - exact Har.
                -
                intros key value Hget. specialize (Hbouter _ _ Hget) as [P Z].
                split; [exact P|]. exact Z. }
              assert (Hmapl : all_keys
                  (fun k => matches_prefix k lp lm = true /\ zero_bit k lm = true)
                  (map_left f ll)).
              { eapply all_keys_map_left; eauto. }
              split.
              ** apply branch_wf; assumption.
              ** intro key. rewrite get_branch by assumption.
                 change
                   ((if matches_prefix key lp lm then
                       if zero_bit key lm
                       then get key (map_left f ll)
                       else get key (combine_fuel fuel f lr (Branch rp rm rl rr))
                     else None) =
                    f (if matches_prefix key lp lm then
                         if zero_bit key lm then get key ll else get key lr
                       else None)
                      (get key (Branch rp rm rl rr))).
                 destruct (matches_prefix key lp lm) eqn:P.
                 --- destruct (zero_bit key lm) eqn:Z.
                     +++ rewrite Hmap.
                         assert (get key (Branch rp rm rl rr) = None) as RB.
                         { eapply all_keys_none; [exact Hbouter|].
                           cbn. intuition congruence. }
                         rewrite RB. destruct (get key ll); cbn;
                           [reflexivity|symmetry; exact Hnone].
                     +++ apply Hco.
                 --- assert (get key (Branch rp rm rl rr) = None) as RB.
                     { eapply all_keys_none; [exact Hbouter|].
                       cbn. intuition congruence. }
                     rewrite RB. symmetry. exact Hnone.
        -- rewrite Hrepb, KBmatch.
           destruct (map_left_correct_wf f Hwl) as [Hwma Hma].
           destruct (map_right_correct_wf f Hwr) as [Hwmb Hmb].
           assert (Haprefix : all_keys (fun k => matches_prefix k lp lm = true)
               (Branch lp lm ll lr)) by (now apply branch_all_prefix).
           assert (Hmapa_prefix : all_keys (fun k => matches_prefix k lp lm = true)
               (map_left f (Branch lp lm ll lr))).
           { eapply all_keys_map_left; eauto. }
           assert (Hmapb_prefix : all_keys (fun k => matches_prefix k rp rm = true)
               (map_right f (Branch rp rm rl rr))).
           { eapply all_keys_map_right; eauto. }
           assert (Hd : forall ak av bk bv,
               get ak (map_left f (Branch lp lm ll lr)) = Some av ->
               get bk (map_right f (Branch rp rm rl rr)) = Some bv ->
               (lm < highest_differing_bit ak bk)%N /\
               (rm < highest_differing_bit ak bk)%N).
           { intros ak av bk bv Eak Ebk.
             destruct (@map_left_binding_source A B C f
               (Branch lp lm ll lr) Hwl ak av Eak) as [aold Aold].
             destruct (@map_right_binding_source A B C f
               (Branch rp rm rl rr) Hwr bk bv Ebk) as [bold Bold].
             pose proof (Haprefix _ _ Aold) as Apre.
             pose proof (Hbouter0 _ _ Bold) as [Bpre Bbit].
             unfold matches_prefix in Apre, Bpre, KBmatch.
             apply N.eqb_eq in Apre. apply N.eqb_eq in Bpre.
             apply N.eqb_neq in KBmatch.
             assert (Hdiff : prefix ak lm <> prefix bk lm) by congruence.
             pose proof (prefix_mismatch_highest_above ak bk lm Hdiff) as Hhigh.
             split; [exact Hhigh|lia]. }
           destruct (@join_disjoint_correct C
             (map_left f (Branch lp lm ll lr))
             (map_right f (Branch rp rm rl rr)) lp lm rp rm
             Hwma Hwmb Hmapa_prefix Hmapb_prefix Hd)
             as [Hwj Hjoin].
           split; [exact Hwj|]. intro key. rewrite Hjoin, Hma, Hmb.
           destruct (get key (Branch lp lm ll lr)) as [av|] eqn:EA;
             destruct (get key (Branch rp rm rl rr)) as [bv|] eqn:EB; cbn.
           ++ pose proof (Haprefix _ _ EA) as AP.
              pose proof (Hbouter0 _ _ EB) as [BP BZ].
              unfold matches_prefix in AP, BP, KBmatch.
              apply N.eqb_eq in AP. apply N.eqb_eq in BP.
              apply N.eqb_neq in KBmatch. exfalso. congruence.
           ++ now destruct (f (Some av) None).
           ++ now destruct (f None (Some bv)).
           ++ symmetry. exact Hnone.
      * destruct (mask_above rm lm) eqn:Mba.
        -- apply mask_above_spec in Mba.
           destruct (representative ll) as [ka|] eqn:Ra.
           2:{ apply (representative_none_wf Hwall) in Ra. subst ll.
               destruct Hnall as [key [value E]]. discriminate. }
           assert (Hrepa : representative (Branch lp lm ll lr) = Some ka).
           { cbn [representative]. now rewrite Ra. }
           destruct (representative_get_wf Hwl Hrepa) as [kav Hgetka].
           assert (Haprefix : all_keys (fun k => matches_prefix k lp lm = true)
               (Branch lp lm ll lr)) by (now apply branch_all_prefix).
           assert (Hkanot : get ka (Branch lp lm ll lr) <> None) by
             (rewrite Hgetka; discriminate).
           pose proof (@all_keys_uniform_above A (Branch lp lm ll lr)
             lp lm ka rm Haprefix Mba Hkanot) as Haouter0.
           destruct (matches_prefix ka rp rm) eqn:KAmatch.
           ++ assert (Haouter : all_keys
                 (fun k => matches_prefix k rp rm = true /\
                           zero_bit k rm = zero_bit ka rm)
                 (Branch lp lm ll lr)).
              { intros key value Hget. specialize (Haouter0 _ _ Hget) as [P Z].
                split; [|exact Z]. unfold matches_prefix in P, KAmatch |- *.
                apply N.eqb_eq in P. apply N.eqb_eq in KAmatch. apply N.eqb_eq.
                congruence. }
              destruct (zero_bit ka rm) eqn:KAzero.
              ** rewrite Hrepa, KAmatch, KAzero.
                 destruct (IH f (Branch lp lm ll lr) rl Hnone Hwl Hwbrl Hsalr)
                   as [Hwco Hco].
                 destruct (map_right_correct_wf f Hwbrr) as [Hwmap Hmap].
                 assert (Hcol : all_keys
                     (fun k => matches_prefix k rp rm = true /\ zero_bit k rm = true)
                     (combine_fuel fuel f (Branch lp lm ll lr) rl)).
                 { eapply all_keys_of_combine_lookup.
                   - exact Hnone.
                   - exact Hco.
                   - intros key value Hget.
                     specialize (Haouter _ _ Hget) as [P Z]. split; [exact P|exact Z].
                   - exact Hbl. }
                 assert (Hmapr : all_keys
                     (fun k => matches_prefix k rp rm = true /\ zero_bit k rm = false)
                     (map_right f rr)).
                 { eapply all_keys_map_right; eauto. }
                 split.
                 --- apply branch_wf; assumption.
                 --- intro key. rewrite get_branch by assumption.
                     change
                       ((if matches_prefix key rp rm then
                           if zero_bit key rm
                           then get key (combine_fuel fuel f (Branch lp lm ll lr) rl)
                           else get key (map_right f rr)
                         else None) =
                        f (get key (Branch lp lm ll lr))
                          (if matches_prefix key rp rm then
                             if zero_bit key rm then get key rl else get key rr
                           else None)).
                     destruct (matches_prefix key rp rm) eqn:P.
                     +++ destruct (zero_bit key rm) eqn:Z.
                         *** apply Hco.
                         *** rewrite Hmap.
                             assert (get key (Branch lp lm ll lr) = None) as LA.
                             { eapply all_keys_none; [exact Haouter|].
                               cbn. intuition congruence. }
                             rewrite LA. destruct (get key rr); cbn;
                               [reflexivity|symmetry; exact Hnone].
                     +++ assert (get key (Branch lp lm ll lr) = None) as LA.
                         { eapply all_keys_none; [exact Haouter|].
                           cbn. intuition congruence. }
                         rewrite LA. symmetry. exact Hnone.
              ** rewrite Hrepa, KAmatch, KAzero.
                 destruct (IH f (Branch lp lm ll lr) rr Hnone Hwl Hwbrr Hsarr)
                   as [Hwco Hco].
                 destruct (map_right_correct_wf f Hwbrl) as [Hwmap Hmap].
                 assert (Hcor : all_keys
                     (fun k => matches_prefix k rp rm = true /\ zero_bit k rm = false)
                     (combine_fuel fuel f (Branch lp lm ll lr) rr)).
                 { eapply all_keys_of_combine_lookup.
                   - exact Hnone.
                   - exact Hco.
                   - intros key value Hget.
                     specialize (Haouter _ _ Hget) as [P Z]. split; [exact P|exact Z].
                   - exact Hbr. }
                 assert (Hmapl : all_keys
                     (fun k => matches_prefix k rp rm = true /\ zero_bit k rm = true)
                     (map_right f rl)).
                 { eapply all_keys_map_right; eauto. }
                 split.
                 --- apply branch_wf; assumption.
                 --- intro key. rewrite get_branch by assumption.
                     change
                       ((if matches_prefix key rp rm then
                           if zero_bit key rm
                           then get key (map_right f rl)
                           else get key (combine_fuel fuel f (Branch lp lm ll lr) rr)
                         else None) =
                        f (get key (Branch lp lm ll lr))
                          (if matches_prefix key rp rm then
                             if zero_bit key rm then get key rl else get key rr
                           else None)).
                     destruct (matches_prefix key rp rm) eqn:P.
                     +++ destruct (zero_bit key rm) eqn:Z.
                         *** rewrite Hmap.
                             assert (get key (Branch lp lm ll lr) = None) as LA.
                             { eapply all_keys_none; [exact Haouter|].
                               cbn. intuition congruence. }
                             rewrite LA. destruct (get key rl); cbn;
                               [reflexivity|symmetry; exact Hnone].
                         *** apply Hco.
                     +++ assert (get key (Branch lp lm ll lr) = None) as LA.
                         { eapply all_keys_none; [exact Haouter|].
                           cbn. intuition congruence. }
                         rewrite LA. symmetry. exact Hnone.
           ++ rewrite Hrepa, KAmatch.
              destruct (map_left_correct_wf f Hwl) as [Hwma Hma].
              destruct (map_right_correct_wf f Hwr) as [Hwmb Hmb].
              assert (Hbprefix : all_keys (fun k => matches_prefix k rp rm = true)
                  (Branch rp rm rl rr)) by (now apply branch_all_prefix).
              assert (Hmapa_prefix : all_keys (fun k => matches_prefix k lp lm = true)
                  (map_left f (Branch lp lm ll lr))).
              { eapply all_keys_map_left; eauto. }
              assert (Hmapb_prefix : all_keys (fun k => matches_prefix k rp rm = true)
                  (map_right f (Branch rp rm rl rr))).
              { eapply all_keys_map_right; eauto. }
              assert (Hd : forall ak av bk bv,
                  get ak (map_left f (Branch lp lm ll lr)) = Some av ->
                  get bk (map_right f (Branch rp rm rl rr)) = Some bv ->
                  (lm < highest_differing_bit ak bk)%N /\
                  (rm < highest_differing_bit ak bk)%N).
              { intros ak av bk bv Eak Ebk.
                destruct (@map_left_binding_source A B C f
                  (Branch lp lm ll lr) Hwl ak av Eak) as [aold Aold].
                destruct (@map_right_binding_source A B C f
                  (Branch rp rm rl rr) Hwr bk bv Ebk) as [bold Bold].
                pose proof (Haouter0 _ _ Aold) as [Apre Abit].
                pose proof (Hbprefix _ _ Bold) as Bpre.
                unfold matches_prefix in Apre, Bpre, KAmatch.
                apply N.eqb_eq in Apre. apply N.eqb_eq in Bpre.
                apply N.eqb_neq in KAmatch.
                assert (Hdiff : prefix ak rm <> prefix bk rm) by congruence.
                pose proof (prefix_mismatch_highest_above ak bk rm Hdiff) as Hhigh.
                split; [lia|exact Hhigh]. }
              destruct (@join_disjoint_correct C
                (map_left f (Branch lp lm ll lr))
                (map_right f (Branch rp rm rl rr)) lp lm rp rm
                Hwma Hwmb Hmapa_prefix Hmapb_prefix Hd)
                as [Hwj Hjoin].
              split; [exact Hwj|]. intro key. rewrite Hjoin, Hma, Hmb.
              destruct (get key (Branch lp lm ll lr)) as [av|] eqn:EA;
                destruct (get key (Branch rp rm rl rr)) as [bv|] eqn:EB; cbn.
              ** pose proof (Haouter0 _ _ EA) as [AP AZ].
                 pose proof (Hbprefix _ _ EB) as BP.
                 unfold matches_prefix in AP, BP, KAmatch.
                 apply N.eqb_eq in AP. apply N.eqb_eq in BP.
                 apply N.eqb_neq in KAmatch. exfalso. congruence.
              ** now destruct (f (Some av) None).
              ** now destruct (f None (Some bv)).
              ** symmetry. exact Hnone.
        -- assert (Hle1 : (lm <= rm)%N).
           { unfold mask_above in Mab. now apply N.ltb_ge in Mab. }
           assert (Hle2 : (rm <= lm)%N).
           { unfold mask_above in Mba. now apply N.ltb_ge in Mba. }
           assert (Hmasks : lm = rm) by lia. subst rm.
           assert (Hprefix_neq : lp <> rp).
           { rewrite N.eqb_refl in Same. cbn in Same.
             now apply N.eqb_neq in Same. }
           destruct (map_left_correct_wf f Hwl) as [Hwma Hma].
           destruct (map_right_correct_wf f Hwr) as [Hwmb Hmb].
           assert (Haprefix : all_keys (fun k => matches_prefix k lp lm = true)
               (Branch lp lm ll lr)) by (now apply branch_all_prefix).
           assert (Hbprefix : all_keys (fun k => matches_prefix k rp lm = true)
               (Branch rp lm rl rr)) by (now apply branch_all_prefix).
           assert (Hmapa_prefix : all_keys (fun k => matches_prefix k lp lm = true)
               (map_left f (Branch lp lm ll lr))).
           { eapply all_keys_map_left; eauto. }
           assert (Hmapb_prefix : all_keys (fun k => matches_prefix k rp lm = true)
               (map_right f (Branch rp lm rl rr))).
           { eapply all_keys_map_right; eauto. }
           assert (Hd : forall ak av bk bv,
               get ak (map_left f (Branch lp lm ll lr)) = Some av ->
               get bk (map_right f (Branch rp lm rl rr)) = Some bv ->
               (lm < highest_differing_bit ak bk)%N /\
               (lm < highest_differing_bit ak bk)%N).
           { intros ak av bk bv Eak Ebk.
             destruct (@map_left_binding_source A B C f
               (Branch lp lm ll lr) Hwl ak av Eak) as [aold Aold].
             destruct (@map_right_binding_source A B C f
               (Branch rp lm rl rr) Hwr bk bv Ebk) as [bold Bold].
             pose proof (Haprefix _ _ Aold) as AP.
             pose proof (Hbprefix _ _ Bold) as BP.
             unfold matches_prefix in AP, BP.
             apply N.eqb_eq in AP. apply N.eqb_eq in BP.
             assert (Hdiff : prefix ak lm <> prefix bk lm) by congruence.
             pose proof (prefix_mismatch_highest_above ak bk lm Hdiff) as Hhigh.
             split; exact Hhigh. }
           destruct (@join_disjoint_correct C
             (map_left f (Branch lp lm ll lr))
             (map_right f (Branch rp lm rl rr)) lp lm rp lm
             Hwma Hwmb Hmapa_prefix Hmapb_prefix Hd)
             as [Hwj Hjoin].
           split; [exact Hwj|]. intro key. rewrite Hjoin, Hma, Hmb.
           destruct (get key (Branch lp lm ll lr)) as [av|] eqn:EA;
             destruct (get key (Branch rp lm rl rr)) as [bv|] eqn:EB; cbn.
           ++ pose proof (Haprefix _ _ EA) as AP.
              pose proof (Hbprefix _ _ EB) as BP.
              unfold matches_prefix in AP, BP.
              apply N.eqb_eq in AP. apply N.eqb_eq in BP.
              exfalso. apply Hprefix_neq. congruence.
           ++ now destruct (f (Some av) None).
           ++ now destruct (f None (Some bv)).
           ++ symmetry. exact Hnone.
Qed.

Theorem combine_correct_wf:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (left : t A) (right : t B),
    f None None = None -> wf left -> wf right ->
    wf (combine f left right) /\
    forall key, get key (combine f left right) = f (get key left) (get key right).
Proof.
  intros. unfold combine.
  rewrite combine_structural_eq_public_combine_fuel.
  eapply combine_fuel_correct_wf; eauto.
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
  destruct (@combine_correct_wf A A A
    (fun x y => match x with Some _ => x | None => y end)
    left right eq_refl Hleft Hright) as [Hwf Hget].
  split; [exact Hwf|].
  intro key. rewrite Hget. now destruct (get key left).
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
  destruct (@combine_correct_wf A A A
    (fun x y => match y with Some _ => y | None => x end)
    left right eq_refl Hleft Hright) as [Hwf Hget].
  split; [exact Hwf|].
  intro key. rewrite Hget. now destruct (get key right).
Qed.

(** Small exact-result certificates for the specialized worker.  They are the
    source counterparts of the native realizer's no-change and immediate-join
    paths; the forthcoming general refinement theorem composes them through
    recursive overlap cases. *)
Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros. reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. intros. reflexivity. Qed.

Theorem union_left_specialized_disjoint_masks:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    mask_above ma mb = false ->
    mask_above mb ma = false ->
    union_left_specialized (Branch pa ma la ra) (Branch pb mb lb rb) =
    join (Branch pa ma la ra) (Branch pb mb lb rb).
Proof.
  intros A pa ma la ra pb mb lb rb Hab Hba.
  cbn [union_left_specialized]. rewrite Hab, Hba. reflexivity.
Qed.

Lemma wf_empty_ok:
  forall A, @wf A empty.
Proof. constructor. Qed.

Lemma wf_singleton_ok:
  forall A k (v : A), wf (singleton k v).
Proof. constructor. Qed.

Definition sample_a : t N :=
  set 12 120%N (set 4 40%N (set 7 70%N empty)).

Definition sample_b : t N :=
  set 13 130%N (set 4 400%N (set 2 20%N empty)).

Definition add_options (a b : option N) : option N :=
  match a, b with
  | None, None => None
  | Some x, None => Some x
  | None, Some y => Some y
  | Some x, Some y => Some (x + y)%N
  end.

Example set_lookup_hit: get 7 sample_a = Some 70%N.
Proof. vm_compute. reflexivity. Qed.

Example set_lookup_miss: get 8 sample_a = None.
Proof. vm_compute. reflexivity. Qed.

Example remove_lookup_hit: get 4 (remove 4 sample_a) = None.
Proof. vm_compute. reflexivity. Qed.

Example remove_preserves_other: get 7 (remove 4 sample_a) = Some 70%N.
Proof. vm_compute. reflexivity. Qed.

Example combine_overlap:
  get 4 (combine add_options sample_a sample_b) = Some 440%N.
Proof. vm_compute. reflexivity. Qed.

Example combine_left_only:
  get 12 (combine add_options sample_a sample_b) = Some 120%N.
Proof. vm_compute. reflexivity. Qed.

Example combine_right_only:
  get 2 (combine add_options sample_a sample_b) = Some 20%N.
Proof. vm_compute. reflexivity. Qed.

Example left_biased_overlap:
  get 4 (union_left sample_a sample_b) = Some 40%N.
Proof. vm_compute. reflexivity. Qed.
