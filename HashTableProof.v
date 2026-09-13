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

End WellFormed.

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

Lemma get_tree_leaf_same :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    eqb key key = true ->
    get_tree eqb fuel depth full_hash key (Leaf full_hash key value) = Some value.
Proof.
  intros K A eqb fuel depth full_hash key value Heqb.
  destruct fuel; simpl; now rewrite N.eqb_refl, Heqb.
Qed.

Lemma get_tree_leaf_other_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash stored_hash
         key stored (value : A),
    full_hash <> stored_hash ->
    get_tree eqb fuel depth full_hash key (Leaf stored_hash stored value) = None.
Proof.
  intros K A eqb fuel depth full_hash stored_hash key stored value Hneq.
  destruct fuel; simpl; apply N.eqb_neq in Hneq; now rewrite Hneq.
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

Lemma remove_tree_leaf_removes :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    eqb key key = true ->
    remove_tree eqb fuel depth full_hash key (Leaf full_hash key value) = Empty.
Proof.
  intros K A eqb fuel depth full_hash key value Heqb.
  destruct fuel; simpl; now rewrite N.eqb_refl, Heqb.
Qed.

Lemma get_tree_collision_same_hash :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash query
         (entries : list (K * A)),
    get_tree eqb fuel depth full_hash query (Collision full_hash entries) =
    bucket_get eqb query entries.
Proof. intros. destruct fuel; cbn [get_tree]; now rewrite N.eqb_refl. Qed.

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

Lemma set_tree_empty_bindings :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key
         (value : A),
    bindings (set_tree eqb fuel depth full_hash key value Empty) = [(key, value)].
Proof. intros. destruct fuel; reflexivity. Qed.

Lemma remove_tree_empty_bindings :
  forall (K A : Type) (eqb : K -> K -> bool) fuel depth full_hash key,
    @bindings K A (remove_tree eqb fuel depth full_hash key Empty) = [].
Proof. intros. destruct fuel; reflexivity. Qed.
