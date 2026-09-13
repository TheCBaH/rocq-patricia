(** Collision buckets for equal full hashes.

    A bucket compares only keys and never values.  Replacement preserves the
    resident key representative; this is the representative-retention rule
    required by the public functor. *)

From Stdlib Require Import Bool Lia List NArith SetoidList.
Import ListNotations.

Set Implicit Arguments.

Fixpoint bucket_get {K A : Type} (eqb : K -> K -> bool)
    (query : K) (entries : list (K * A)) : option A :=
  match entries with
  | [] => None
  | (stored, value) :: tail =>
      if eqb query stored then Some value else bucket_get eqb query tail
  end.

Fixpoint bucket_set {K A : Type} (eqb : K -> K -> bool)
    (key : K) (value : A) (entries : list (K * A)) : list (K * A) :=
  match entries with
  | [] => [(key, value)]
  | (stored, old_value) :: tail =>
      if eqb key stored
      then (stored, value) :: tail
      else (stored, old_value) :: bucket_set eqb key value tail
  end.

Fixpoint bucket_remove {K A : Type} (eqb : K -> K -> bool)
    (key : K) (entries : list (K * A)) : list (K * A) :=
  match entries with
  | [] => []
  | (stored, value) :: tail =>
      if eqb key stored then tail
      else (stored, value) :: bucket_remove eqb key tail
  end.

Inductive normalized_bucket (K A : Type) : Type :=
| BucketEmpty
| BucketLeaf (entry : K * A)
| BucketMany (entries : list (K * A)).

Arguments BucketEmpty {K A}.
Arguments BucketLeaf {K A} _.
Arguments BucketMany {K A} _.

Definition normalize_bucket {K A : Type}
    (entries : list (K * A)) : normalized_bucket K A :=
  match entries with
  | [] => BucketEmpty
  | [entry] => BucketLeaf entry
  | _ => BucketMany entries
  end.

Lemma bucket_get_empty :
  forall K A (eqb : K -> K -> bool) query,
    @bucket_get K A eqb query [] = None.
Proof. reflexivity. Qed.

Lemma bucket_set_empty :
  forall K A (eqb : K -> K -> bool) key (value : A),
    bucket_set eqb key value [] = [(key, value)].
Proof. reflexivity. Qed.

Lemma bucket_set_retains_head_representative :
  forall K A (eqb : K -> K -> bool) key stored (old value : A) tail,
    eqb key stored = true ->
    bucket_set eqb key value ((stored, old) :: tail) = (stored, value) :: tail.
Proof. intros. simpl. now rewrite H. Qed.

Lemma bucket_remove_head :
  forall K A (eqb : K -> K -> bool) key stored (value : A) tail,
    eqb key stored = true ->
    bucket_remove eqb key ((stored, value) :: tail) = tail.
Proof. intros. simpl. now rewrite H. Qed.

Lemma bucket_get_after_set :
  forall K A (eqb : K -> K -> bool),
    (forall key, eqb key key = true) ->
    forall key (value : A) entries,
      bucket_get eqb key (bucket_set eqb key value entries) = Some value.
Proof.
  intros K A eqb Heqb key value entries.
  induction entries as [|[stored old] tail IH]; simpl.
  - now rewrite Heqb.
  - destruct (eqb key stored) eqn:Hstored; simpl; now rewrite Hstored.
Qed.

Lemma bucket_get_set_other :
  forall K A (eqb : K -> K -> bool),
    (forall left right, eqb left right = eqb right left) ->
    (forall left middle right,
        eqb left middle = true -> eqb middle right = true -> eqb left right = true) ->
    forall query key (value : A) entries,
      eqb query key = false ->
      bucket_get eqb query (bucket_set eqb key value entries) =
      bucket_get eqb query entries.
Proof.
  intros K A eqb Hsymmetric Htrans query key value entries Hdifferent.
  induction entries as [|[stored old_value] tail IH]; simpl.
  - now rewrite Hdifferent.
  - destruct (eqb key stored) eqn:Hkey_stored.
    + assert (Hquery_stored : eqb query stored = false).
      { destruct (eqb query stored) eqn:Hquery_stored; auto.
        assert (Hequal : eqb query key = true).
        { apply Htrans with (middle := stored); auto.
          rewrite Hsymmetric. exact Hkey_stored. }
        rewrite Hdifferent in Hequal. discriminate. }
      cbn [bucket_get]. now rewrite Hquery_stored.
    + destruct (eqb query stored) eqn:Hquery_stored.
      * cbn [bucket_get]. now rewrite Hquery_stored.
      * cbn [bucket_get]. rewrite Hquery_stored. now apply IH.
Qed.

Lemma bucket_get_remove_other :
  forall K A (eqb : K -> K -> bool),
    (forall left right, eqb left right = eqb right left) ->
    (forall left middle right,
        eqb left middle = true -> eqb middle right = true -> eqb left right = true) ->
    forall query key (entries : list (K * A)),
      eqb query key = false ->
      bucket_get eqb query (bucket_remove eqb key entries) =
      bucket_get eqb query entries.
Proof.
  intros K A eqb Hsymmetric Htrans query key entries Hdifferent.
  induction entries as [|[stored value] tail IH]; simpl.
  - reflexivity.
  - destruct (eqb key stored) eqn:Hkey_stored.
    + assert (Hquery_stored : eqb query stored = false).
      { destruct (eqb query stored) eqn:Hquery_stored; auto.
        assert (Hequal : eqb query key = true).
        { apply Htrans with (middle := stored); auto.
          rewrite Hsymmetric. exact Hkey_stored. }
        rewrite Hdifferent in Hequal. discriminate. }
      cbn [bucket_get]. now rewrite Hquery_stored.
    + destruct (eqb query stored) eqn:Hquery_stored.
      * cbn [bucket_get]. now rewrite Hquery_stored.
      * cbn [bucket_get]. rewrite Hquery_stored. now apply IH.
Qed.

Lemma bucket_set_miss :
  forall K A (eqb : K -> K -> bool) key (value : A) (entries : list (K * A)),
    (forall stored old_value, In (stored, old_value) entries -> eqb key stored = false) ->
    bucket_set eqb key value entries = entries ++ [(key, value)].
Proof.
  intros K A eqb key value entries Hmiss.
  induction entries as [|[stored old_value] tail IH]; simpl.
  - reflexivity.
  - assert (Hhead : eqb key stored = false).
    { apply (Hmiss stored old_value). simpl. auto. }
    rewrite Hhead. f_equal. apply IH.
    intros stored' old_value' Hin.
    apply (Hmiss stored' old_value'). simpl. now right.
Qed.

Lemma bucket_set_miss_length :
  forall K A (eqb : K -> K -> bool) key (value : A) (entries : list (K * A)),
    (forall stored old_value, In (stored, old_value) entries -> eqb key stored = false) ->
    length (bucket_set eqb key value entries) = S (length entries).
Proof.
  intros K A eqb key value entries Hmiss.
  rewrite bucket_set_miss by exact Hmiss.
  rewrite length_app. simpl. lia.
Qed.

Lemma nodupA_snoc :
  forall A (R : A -> A -> Prop),
    Symmetric R ->
    forall (entries : list A) entry,
      NoDupA R entries ->
      ~ InA R entry entries ->
      NoDupA R (entries ++ [entry]).
Proof.
  intros A R Hsymmetric entries. induction entries as [|head tail IH]; intros entry Hnodup Hentry.
  - constructor; [intro Hin; inversion Hin|constructor].
  - inversion Hnodup as [|head' tail' Hhead Htail]; subst.
    constructor.
    + intro Hin. apply (proj1 (InA_app_iff R tail [entry] head)) in Hin.
      destruct Hin as [Hintail|Hinentry].
      * now apply Hhead.
      * apply Hentry. apply (proj2 (InA_cons R entry head tail)).
        left. apply Hsymmetric.
        apply (proj1 (InA_cons R head entry [])) in Hinentry.
        destruct Hinentry as [Hinentry|Hinentry]; [exact Hinentry|inversion Hinentry].
    + apply IH; auto.
Qed.

Lemma bucket_set_miss_nodup :
  forall K A (R : K * A -> K * A -> Prop) (eqb : K -> K -> bool)
         key (value : A) (entries : list (K * A)),
    Symmetric R ->
    NoDupA R entries ->
    (forall stored old_value, In (stored, old_value) entries -> eqb key stored = false) ->
    ~ InA R (key, value) entries ->
    NoDupA R (bucket_set eqb key value entries).
Proof.
  intros K A R eqb key value entries Hsymmetric Hnodup Hmiss Hfresh.
  rewrite bucket_set_miss by exact Hmiss.
  now apply nodupA_snoc.
Qed.

Lemma nodupA_replace_head :
  forall K A (R : K * A -> K * A -> Prop) stored old_value new_value tail,
    NoDupA R ((stored, old_value) :: tail) ->
    (forall entry, R (stored, new_value) entry <-> R (stored, old_value) entry) ->
    NoDupA R ((stored, new_value) :: tail).
Proof.
  intros K A R stored old_value new_value tail Hnodup Hstable.
  inversion Hnodup as [|head entries Hnotin Htail]; subst.
  constructor.
  - intro Hin. apply Hnotin.
    apply (proj2 (InA_alt R (stored, old_value) tail)).
    apply (proj1 (InA_alt R (stored, new_value) tail)) in Hin.
    destruct Hin as [entry [Hrelated Hin]].
    exists entry. split; [now apply (proj1 (Hstable entry))|exact Hin].
  - exact Htail.
Qed.

Lemma bucket_set_head_nodup :
  forall K A (R : K * A -> K * A -> Prop) (eqb : K -> K -> bool)
         key stored (old_value new_value : A) tail,
    eqb key stored = true ->
    NoDupA R ((stored, old_value) :: tail) ->
    (forall entry, R (stored, new_value) entry <-> R (stored, old_value) entry) ->
    NoDupA R (bucket_set eqb key new_value ((stored, old_value) :: tail)).
Proof.
  intros K A R eqb key stored old_value new_value tail Hmatch Hnodup Hstable.
  rewrite (bucket_set_retains_head_representative eqb key stored old_value new_value tail Hmatch).
  eapply nodupA_replace_head; eauto.
Qed.

Lemma bucket_set_length_hit :
  forall K A (eqb : K -> K -> bool) key (value : A) (entries : list (K * A)),
    bucket_get eqb key entries <> None ->
    length (bucket_set eqb key value entries) = length entries.
Proof.
  intros K A eqb key value entries.
  induction entries as [|[stored old_value] tail IH]; intro Hhit; simpl in Hhit.
  - contradiction.
  - destruct (eqb key stored) eqn:Hstored.
    + simpl. now rewrite Hstored.
    + simpl. rewrite Hstored. simpl. now rewrite (IH Hhit).
Qed.

Lemma bucket_remove_miss :
  forall K A (eqb : K -> K -> bool) key (entries : list (K * A)),
    (forall stored value, In (stored, value) entries -> eqb key stored = false) ->
    bucket_remove eqb key entries = entries.
Proof.
  intros K A eqb key entries Hmiss.
  induction entries as [|[stored value] tail IH]; simpl; auto.
  assert (Hhead : eqb key stored = false).
  { apply (Hmiss stored value). simpl. auto. }
  rewrite Hhead. f_equal.
  apply IH. intros stored' value' Hin.
  apply (Hmiss stored' value'). simpl. now right.
Qed.

Lemma bucket_get_miss :
  forall K A (eqb : K -> K -> bool) key (entries : list (K * A)),
    (forall stored value, In (stored, value) entries -> eqb key stored = false) ->
    bucket_get eqb key entries = None.
Proof.
  intros K A eqb key entries Hmiss.
  induction entries as [|[stored value] tail IH]; simpl; auto.
  assert (Hhead : eqb key stored = false).
  { apply (Hmiss stored value). simpl. auto. }
  rewrite Hhead. apply IH.
  intros stored' value' Hin. apply (Hmiss stored' value'). simpl. now right.
Qed.

Lemma bucket_remove_length_le :
  forall K A (eqb : K -> K -> bool) key (entries : list (K * A)),
    length (bucket_remove eqb key entries) <= length entries.
Proof.
  intros K A eqb key entries.
  induction entries as [|[stored value] tail IH]; simpl; auto with arith.
  destruct (eqb key stored); simpl; auto with arith.
Qed.

Lemma bucket_remove_length_hit :
  forall K A (eqb : K -> K -> bool) key (entries : list (K * A)),
    bucket_get eqb key entries <> None ->
    length (bucket_remove eqb key entries) = Nat.pred (length entries).
Proof.
  intros K A eqb key entries.
  induction entries as [|[stored value] tail IH]; intro Hhit; simpl in Hhit.
  - contradiction.
  - destruct (eqb key stored) eqn:Hstored.
    + simpl. now rewrite Hstored.
    + simpl. rewrite Hstored.
      specialize (IH Hhit).
      destruct tail as [|[next_key next_value] rest].
      * simpl in Hhit. contradiction.
      * simpl in IH. simpl. rewrite IH. reflexivity.
Qed.

Lemma bucket_remove_inA :
  forall K A (R : K * A -> K * A -> Prop) (eqb : K -> K -> bool)
         key (entries : list (K * A)) entry,
    InA R entry (bucket_remove eqb key entries) -> InA R entry entries.
Proof.
  intros K A R eqb key entries.
  induction entries as [|[stored value] tail IH]; intros entry Hin; simpl in Hin.
  - inversion Hin.
  - destruct (eqb key stored) eqn:Hstored.
    + apply InA_cons_tl. exact Hin.
    + apply (proj2 (InA_cons R entry (stored, value) tail)).
      destruct (proj1
        (InA_cons R entry (stored, value) (bucket_remove eqb key tail)) Hin)
        as [Hhead|Htail].
      * now left.
      * right. now apply IH.
Qed.

Lemma bucket_remove_nodup :
  forall K A (R : K * A -> K * A -> Prop) (eqb : K -> K -> bool)
         key (entries : list (K * A)),
    NoDupA R entries -> NoDupA R (bucket_remove eqb key entries).
Proof.
  intros K A R eqb key entries Hnodup.
  induction entries as [|[stored value] tail IH]; simpl.
  - constructor.
  - inversion Hnodup as [|entry entries Hnotin Htail]; subst.
    destruct (eqb key stored) eqn:Hstored.
    + exact Htail.
    + constructor.
      * intro Hin. apply Hnotin. now apply bucket_remove_inA in Hin.
      * now apply IH.
Qed.

Lemma normalize_bucket_empty :
  forall K A, @normalize_bucket K A [] = BucketEmpty.
Proof. reflexivity. Qed.

Lemma normalize_bucket_singleton :
  forall K A (entry : K * A), normalize_bucket [entry] = BucketLeaf entry.
Proof. reflexivity. Qed.

Lemma normalize_bucket_many :
  forall K A (first second : K * A) tail,
    normalize_bucket (first :: second :: tail) = BucketMany (first :: second :: tail).
Proof. reflexivity. Qed.
