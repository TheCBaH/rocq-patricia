(** Executable list-backed bitmap HAMT source model.

    This is the H2 source representation.  It is purely functional and keeps
    the seed at the table boundary; raw hashes are computed once by the public
    operation and then threaded through six bounded routing levels. *)

From Stdlib Require Import Bool List NArith.
Import ListNotations.

Require Import HashTableSpec HashTableBits HashTableBucket.

Set Implicit Arguments.

Inductive tree (K A : Type) : Type :=
| Empty
| Leaf (full_hash : N) (key : K) (value : A)
| Collision (full_hash : N) (entries : list (K * A))
| Branch (bitmap : N) (children : list (tree K A)).

Arguments Empty {K A}.
Arguments Leaf {K A} _ _ _.
Arguments Collision {K A} _ _.
Arguments Branch {K A} _ _.

Record table (K Seed A : Type) : Type := {
  table_seed : Seed;
  table_root : tree K A
}.

Definition empty {K Seed A : Type} (seed : Seed) : table K Seed A :=
  {| table_seed := seed; table_root := Empty |}.

Definition is_empty {K Seed A : Type} (m : table K Seed A) : bool :=
  match table_root m with Empty => true | _ => false end.

Fixpoint bindings {K A : Type} (t : tree K A) : list (K * A) :=
  match t with
  | Empty => []
  | Leaf _ key value => [(key, value)]
  | Collision _ entries => entries
  | Branch _ children => flat_map bindings children
  end.

Definition elements {K Seed A : Type} (m : table K Seed A) : list (K * A) :=
  bindings (table_root m).

Fixpoint representative_hash {K A : Type} (t : tree K A) : option N :=
  match t with
  | Empty => None
  | Leaf h _ _ => Some h
  | Collision h _ => Some h
  | Branch _ children =>
      match children with [] => None | child :: _ => representative_hash child end
  end.

Definition child_bit (h : N) (depth : nat) : N := bitmap_bit (chunk h depth).

Definition normalize_collision {K A : Type} (h : N) (entries : list (K * A))
    : tree K A :=
  match normalize_bucket entries with
  | BucketEmpty => Empty
  | BucketLeaf (key, value) => Leaf h key value
  | BucketMany entries' => Collision h entries'
  end.

Definition join_two {K A : Type} (left_hash : N) (left : tree K A)
    (right_hash : N) (right : tree K A) (depth : nat) : tree K A :=
  let left_slot := chunk left_hash depth in
  let right_slot := chunk right_hash depth in
  let bitmap := N.lor (bitmap_bit left_slot) (bitmap_bit right_slot) in
  if N.ltb left_slot right_slot
  then Branch bitmap [left; right]
  else Branch bitmap [right; left].

Fixpoint join_worker {K A : Type} (fuel depth : nat)
    (left_hash : N) (left : tree K A)
    (right_hash : N) (right : tree K A) : tree K A :=
  match fuel with
  | O => join_two left_hash left right_hash right depth
  | S fuel' =>
      if N.eqb (chunk left_hash depth) (chunk right_hash depth)
      then Branch (child_bit left_hash depth)
             [join_worker fuel' (S depth) left_hash left right_hash right]
      else join_two left_hash left right_hash right depth
  end.

Fixpoint get_tree {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (query : K) (t : tree K A) : option A :=
  match fuel, t with
  | _, Empty => None
  | _, Leaf stored_hash stored value =>
      if N.eqb full_hash stored_hash then
        if eqb query stored then Some value else None
      else None
  | _, Collision stored_hash entries =>
      if N.eqb full_hash stored_hash then bucket_get eqb query entries else None
  | O, Branch _ _ => None
  | S fuel', Branch bitmap children =>
      let slot := chunk full_hash depth in
      if bitmap_has bitmap slot
      then match dense_get (rank bitmap slot) children with
           | Some child => get_tree eqb fuel' (S depth) full_hash query child
           | None => None
           end
      else None
  end.

Definition get {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (query : K) (m : table K Seed A) : option A :=
  get_tree eqb branch_levels 0 (hash (table_seed m) query) query (table_root m).

Definition mem {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (query : K) (m : table K Seed A) : bool :=
  match get eqb hash query m with Some _ => true | None => false end.

Definition branch_insert {K A : Type} (bitmap : N) (slot : N)
    (child : tree K A) (children : list (tree K A)) : tree K A :=
  Branch (N.lor bitmap (bitmap_bit slot)) (dense_insert (rank bitmap slot) child children).

Definition branch_replace {K A : Type} (bitmap : N) (slot : N)
    (child : tree K A) (children : list (tree K A)) : tree K A :=
  Branch bitmap (dense_replace (rank bitmap slot) child children).

Fixpoint set_tree {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (value : A) (t : tree K A)
    : tree K A :=
  match t with
  | Empty => Leaf full_hash key value
  | Leaf stored_hash stored old =>
      if eqb key stored then Leaf stored_hash stored value
      else if N.eqb full_hash stored_hash
           then Collision stored_hash [(stored, old); (key, value)]
           else join_worker fuel depth full_hash (Leaf full_hash key value)
                  stored_hash (Leaf stored_hash stored old)
  | Collision stored_hash entries =>
      if N.eqb full_hash stored_hash
      then normalize_collision stored_hash (bucket_set eqb key value entries)
      else join_worker fuel depth full_hash (Leaf full_hash key value)
             stored_hash (Collision stored_hash entries)
  | Branch bitmap children =>
      match fuel with
      | O => t
      | S fuel' =>
          let slot := chunk full_hash depth in
          if bitmap_has bitmap slot
          then match dense_get (rank bitmap slot) children with
               | Some child =>
                   branch_replace bitmap slot
                     (set_tree eqb fuel' (S depth) full_hash key value child) children
               | None => branch_insert bitmap slot (Leaf full_hash key value) children
               end
          else branch_insert bitmap slot (Leaf full_hash key value) children
      end
  end.

Definition set {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (key : K) (value : A) (m : table K Seed A)
    : table K Seed A :=
  {| table_seed := table_seed m;
     table_root := set_tree eqb branch_levels 0 (hash (table_seed m) key)
                  key value (table_root m) |}.

Definition branch_remove {K A : Type} (bitmap : N) (slot : N)
    (children : list (tree K A)) : tree K A :=
  let children' := dense_remove (rank bitmap slot) children in
  match children' with
  | [] => Empty
  | _ => Branch (N.ldiff bitmap (bitmap_bit slot)) children'
  end.

Fixpoint remove_tree {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (t : tree K A) : tree K A :=
  match fuel, t with
  | _, Empty => Empty
  | _, Leaf stored_hash stored value =>
      if N.eqb full_hash stored_hash then
        if eqb key stored then Empty else Leaf stored_hash stored value
      else Leaf stored_hash stored value
  | _, Collision stored_hash entries =>
      if N.eqb full_hash stored_hash
      then normalize_collision stored_hash (bucket_remove eqb key entries)
      else Collision stored_hash entries
  | O, Branch _ _ => t
  | S fuel', Branch bitmap children =>
      let slot := chunk full_hash depth in
      if bitmap_has bitmap slot
      then match dense_get (rank bitmap slot) children with
           | None => t
           | Some child =>
               let child' := remove_tree eqb fuel' (S depth) full_hash key child in
               match child' with
               | Empty => branch_remove bitmap slot children
               | _ => branch_replace bitmap slot child' children
               end
           end
      else t
  end.

Definition remove {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (key : K) (m : table K Seed A) : table K Seed A :=
  {| table_seed := table_seed m;
     table_root := remove_tree eqb branch_levels 0 (hash (table_seed m) key)
                  key (table_root m) |}.

Fixpoint add_first {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (bindings : list (K * A)) (m : table K Seed A)
    : table K Seed A :=
  match bindings with
  | [] => m
  | (key, value) :: tail =>
      let m' := match get eqb hash key m with
                | Some _ => m
                | None => set eqb hash key value m
                end in
      add_first eqb hash tail m'
  end.

Definition of_list {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (seed : Seed) (entries : list (K * A))
    : table K Seed A :=
  add_first eqb hash entries (empty seed).

Definition singleton {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (seed : Seed) (key : K) (value : A)
    : table K Seed A :=
  set eqb hash key value (empty seed).

Lemma get_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (query : K),
    @get K Seed A eqb hash query (empty seed) = None.
Proof. reflexivity. Qed.

Lemma get_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (value : A),
      get eqb hash key (singleton eqb hash seed key value) = Some value.
Proof.
  intros K Seed A eqb hash Heqb seed key value.
  unfold singleton, set, get, empty. simpl.
  now rewrite N.eqb_refl, Heqb.
Qed.

Lemma remove_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (key : K),
    @remove K Seed A eqb hash key (empty seed) = empty seed.
Proof. reflexivity. Qed.

Lemma bindings_empty :
  forall (K Seed A : Type) (seed : Seed),
    @elements K Seed A (empty seed) = [].
Proof. reflexivity. Qed.

Lemma bindings_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (key : K) (value : A),
    elements (singleton eqb hash seed key value) = [(key, value)].
Proof. reflexivity. Qed.

Lemma is_empty_empty :
  forall (K Seed A : Type) (seed : Seed),
    @is_empty K Seed A (empty seed) = true.
Proof. reflexivity. Qed.

Lemma is_empty_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (key : K) (value : A),
    is_empty (singleton eqb hash seed key value) = false.
Proof. reflexivity. Qed.

Lemma mem_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (value : A),
      mem eqb hash key (singleton eqb hash seed key value) = true.
Proof.
  intros K Seed A eqb hash Heqb seed key value.
  unfold mem. rewrite get_singleton; auto.
Qed.

Lemma remove_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (value : A),
      remove eqb hash key (singleton eqb hash seed key value) = empty seed.
Proof.
  intros K Seed A eqb hash Heqb seed key value.
  unfold remove, singleton, set, empty. cbn [remove_tree set_tree]. simpl.
  rewrite N.eqb_refl.
  destruct (eqb key key) eqn:Heq.
  - reflexivity.
  - rewrite Heqb in Heq. discriminate.
Qed.

Lemma is_empty_remove_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (value : A),
      is_empty (remove eqb hash key (singleton eqb hash seed key value)) = true.
Proof.
  intros K Seed A eqb hash Heqb seed key value.
  rewrite remove_singleton by exact Heqb.
  apply is_empty_empty.
Qed.

Lemma of_list_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed),
    @of_list K Seed A eqb hash seed [] = empty seed.
Proof. reflexivity. Qed.

Lemma set_seed :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (key : K) (value : A) (m : table K Seed A),
    table_seed (set eqb hash key value m) = table_seed m.
Proof. reflexivity. Qed.

Lemma remove_seed :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (key : K) (m : table K Seed A),
    table_seed (remove eqb hash key m) = table_seed m.
Proof. reflexivity. Qed.

Lemma singleton_seed :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (key : K) (value : A),
    table_seed (singleton eqb hash seed key value) = seed.
Proof. reflexivity. Qed.

Lemma add_first_seed :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         entries (m : table K Seed A),
    table_seed (add_first eqb hash entries m) = table_seed m.
Proof.
  intros K Seed A eqb hash entries.
  induction entries as [|[key value] tail IH]; intros m; simpl; auto.
  destruct (get eqb hash key m).
  - apply IH.
  - rewrite IH. reflexivity.
Qed.

Lemma of_list_seed :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) entries,
    table_seed (@of_list K Seed A eqb hash seed entries) = seed.
Proof. intros. unfold of_list. now rewrite add_first_seed. Qed.
