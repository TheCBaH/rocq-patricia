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

(** The generated induction principle does not recurse through the list of
    branch children.  This nested structural principle carries properties to
    every descendant. *)
Fixpoint tree_ind_nested {K A} (P : tree K A -> Prop)
  (Hempty : P (@Empty K A))
  (Hleaf : forall full_hash key value, P (@Leaf K A full_hash key value))
  (Hcollision : forall full_hash entries, P (@Collision K A full_hash entries))
  (Hbranch : forall bitmap children, Forall P children -> P (@Branch K A bitmap children))
  (t : tree K A) {struct t} : P t :=
  match t with
  | @Empty _ _ => Hempty
  | @Leaf _ _ full_hash key value => Hleaf full_hash key value
  | @Collision _ _ full_hash entries => Hcollision full_hash entries
  | @Branch _ _ bitmap children =>
      Hbranch bitmap children
        ((fix children_ind (children : list (tree K A)) {struct children} :
            Forall P children :=
            match children with
            | [] => Forall_nil _
            | child :: rest =>
                Forall_cons child
                  (@tree_ind_nested K A P Hempty Hleaf Hcollision Hbranch child)
                  (children_ind rest)
            end) children)
  end.

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

Lemma is_empty_root_iff :
  forall (K Seed A : Type) (seed : Seed) (root : tree K A),
    is_empty {| table_seed := seed; table_root := root |} = true <->
    root = Empty.
Proof.
  intros K Seed A seed [|full_hash key value|full_hash entries|bitmap children];
    simpl; split; intro H; try reflexivity; discriminate.
Qed.

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

Lemma child_bit_nonzero :
  forall full_hash depth, child_bit full_hash depth <> 0%N.
Proof.
  intros full_hash depth. unfold child_bit. apply bitmap_bit_nonzero.
Qed.

Lemma child_bit_bound :
  forall full_hash depth,
    (child_bit full_hash depth < bitmap_limit)%N.
Proof.
  intros full_hash depth. unfold child_bit.
  apply bitmap_bit_bound. apply chunk_bound.
Qed.

Lemma child_bit_has_slot :
  forall full_hash depth,
    bitmap_has (child_bit full_hash depth) (chunk full_hash depth) = true.
Proof.
  intros full_hash depth. unfold child_bit. apply bitmap_bit_has_slot.
Qed.

Lemma child_bit_popcount :
  forall full_hash depth,
    popcount32 (child_bit full_hash depth) = 1.
Proof.
  intros full_hash depth. unfold child_bit.
  apply popcount_bitmap_bit. apply chunk_bound.
Qed.

Lemma child_bit_rank_self :
  forall full_hash depth,
    rank (child_bit full_hash depth) (chunk full_hash depth) = 0.
Proof.
  intros full_hash depth. unfold child_bit.
  apply rank_bitmap_bit_self. apply chunk_bound.
Qed.

Lemma child_bit_has_no_other_slot :
  forall full_hash depth slot,
    slot <> chunk full_hash depth ->
    bitmap_has (child_bit full_hash depth) slot = false.
Proof.
  intros full_hash depth slot Hdifferent. unfold child_bit.
  now apply bitmap_bit_has_no_other_slot.
Qed.

Lemma join_two_bitmap_has_left_slot :
  forall left_hash right_hash depth,
    bitmap_has
      (N.lor (bitmap_bit (chunk left_hash depth))
             (bitmap_bit (chunk right_hash depth)))
      (chunk left_hash depth) = true.
Proof.
  intros left_hash right_hash depth. apply bitmap_has_lor_left.
  apply bitmap_bit_has_slot.
Qed.

Lemma join_two_bitmap_has_right_slot :
  forall left_hash right_hash depth,
    bitmap_has
      (N.lor (bitmap_bit (chunk left_hash depth))
             (bitmap_bit (chunk right_hash depth)))
      (chunk right_hash depth) = true.
Proof.
  intros left_hash right_hash depth. apply bitmap_has_lor_right.
  apply bitmap_bit_has_slot.
Qed.

Lemma join_two_bitmap_has_no_other_slot :
  forall left_hash right_hash depth slot,
    slot <> chunk left_hash depth ->
    slot <> chunk right_hash depth ->
    bitmap_has
      (N.lor (bitmap_bit (chunk left_hash depth))
             (bitmap_bit (chunk right_hash depth))) slot = false.
Proof.
  intros left_hash right_hash depth slot Hleft Hright.
  apply bitmap_has_lor_false.
  - now apply bitmap_bit_has_no_other_slot.
  - now apply bitmap_bit_has_no_other_slot.
Qed.

Lemma join_two_bitmap_nonzero :
  forall left_hash right_hash depth,
    N.lor (bitmap_bit (chunk left_hash depth))
          (bitmap_bit (chunk right_hash depth)) <> 0%N.
Proof.
  intros left_hash right_hash depth Hzero.
  pose proof (join_two_bitmap_has_left_slot left_hash right_hash depth) as Hslot.
  rewrite Hzero, bitmap_has_empty in Hslot. discriminate.
Qed.

Lemma join_two_bitmap_bound :
  forall left_hash right_hash depth,
    chunk left_hash depth <> chunk right_hash depth ->
    (N.lor (bitmap_bit (chunk left_hash depth))
           (bitmap_bit (chunk right_hash depth)) < bitmap_limit)%N.
Proof.
  intros left_hash right_hash depth Hdifferent.
  apply bitmap_lor_bound_disjoint.
  - apply bitmap_bit_bound. apply chunk_bound.
  - apply bitmap_bit_bound. apply chunk_bound.
  - apply bitmap_bits_disjoint. exact Hdifferent.
Qed.

Lemma join_two_bitmap_bound_total :
  forall left_hash right_hash depth,
    (N.lor (bitmap_bit (chunk left_hash depth))
           (bitmap_bit (chunk right_hash depth)) < bitmap_limit)%N.
Proof.
  intros left_hash right_hash depth.
  destruct (N.eq_dec (chunk left_hash depth) (chunk right_hash depth)) as [Hequal|Hdifferent].
  - rewrite Hequal, N.lor_diag. apply bitmap_bit_bound. apply chunk_bound.
  - now apply join_two_bitmap_bound.
Qed.

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

Lemma join_two_nonempty :
  forall K A depth left_hash right_hash (left right : tree K A),
    join_two left_hash left right_hash right depth <> Empty.
Proof.
  intros K A depth left_hash right_hash left right.
  unfold join_two. destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth));
    discriminate.
Qed.

Lemma join_worker_nonempty :
  forall K A fuel depth left_hash right_hash (left right : tree K A),
    join_worker fuel depth left_hash left right_hash right <> Empty.
Proof.
  intros K A fuel. induction fuel as [|fuel IH];
    intros depth left_hash right_hash left right.
  - apply join_two_nonempty.
  - cbn [join_worker]. destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)).
    + discriminate.
    + apply join_two_nonempty.
Qed.

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

Lemma mem_spec :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (query : K) (m : table K Seed A),
    mem eqb hash query m = true <->
    exists value, get eqb hash query m = Some value.
Proof.
  intros K Seed A eqb hash query m.
  unfold mem. destruct (get eqb hash query m) as [value|] eqn:Hget; simpl.
  - split; intro H; [now exists value|reflexivity].
  - split; intro H; [discriminate|destruct H as [value Hvalue]; discriminate].
Qed.

Lemma mem_empty :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (query : K),
    mem eqb hash query (@empty K Seed A seed) = false.
Proof. reflexivity. Qed.

Definition branch_insert {K A : Type} (bitmap : N) (slot : N)
    (child : tree K A) (children : list (tree K A)) : tree K A :=
  Branch (N.lor bitmap (bitmap_bit slot)) (dense_insert (rank bitmap slot) child children).

Definition branch_replace {K A : Type} (bitmap : N) (slot : N)
    (child : tree K A) (children : list (tree K A)) : tree K A :=
  Branch bitmap (dense_replace (rank bitmap slot) child children).

Lemma branch_insert_bitmap_bound :
  forall K A (bitmap slot : N) (child : tree K A) (children : list (tree K A)),
    (bitmap < bitmap_limit)%N ->
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = false ->
    match branch_insert bitmap slot child children with
    | Branch bitmap' _ => (bitmap' < bitmap_limit)%N
    | _ => False
    end.
Proof.
  intros K A bitmap slot child children Hbound Hslot Habsent.
  unfold branch_insert. cbn.
  apply bitmap_lor_bit_bound_absent; assumption.
Qed.

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

Lemma branch_remove_bitmap_bound :
  forall K A (bitmap slot : N) (children : list (tree K A)) bitmap' children',
    (bitmap < bitmap_limit)%N ->
    branch_remove bitmap slot children = Branch bitmap' children' ->
    (bitmap' < bitmap_limit)%N.
Proof.
  intros K A bitmap slot children bitmap' children' Hbound Hremove.
  unfold branch_remove in Hremove.
  destruct (dense_remove (rank bitmap slot) children) as [|head tail] eqn:Hdense;
    inversion Hremove; subst; apply bitmap_ldiff_bit_bound; exact Hbound.
Qed.

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

Lemma add_first_cons :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (value : A) tail (m : table K Seed A),
    add_first eqb hash ((key, value) :: tail) m =
    let m' := match get eqb hash key m with
              | Some _ => m
              | None => set eqb hash key value m
              end in
    add_first eqb hash tail m'.
Proof. reflexivity. Qed.

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

Lemma bindings_remove_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (value : A),
      elements (remove eqb hash key (singleton eqb hash seed key value)) = [].
Proof.
  intros K Seed A eqb hash Heqb seed key value.
  rewrite remove_singleton by exact Heqb.
  apply bindings_empty.
Qed.

Lemma of_list_empty :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed),
    @of_list K Seed A eqb hash seed [] = empty seed.
Proof. reflexivity. Qed.

Lemma of_list_singleton :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (key : K) (value : A),
    of_list eqb hash seed [(key, value)] = singleton eqb hash seed key value.
Proof. reflexivity. Qed.

Lemma of_list_first_wins_same_key :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (first second : A),
      of_list eqb hash seed [(key, first); (key, second)] =
      singleton eqb hash seed key first.
Proof.
  intros K Seed A eqb hash Heqb seed key first second.
  change (add_first eqb hash [(key, second)]
    (singleton eqb hash seed key first) = singleton eqb hash seed key first).
  cbn [add_first].
  rewrite get_singleton by exact Heqb.
  reflexivity.
Qed.

Lemma bindings_of_list_first_wins_same_key :
  forall (K Seed A : Type) (eqb : K -> K -> bool) (hash : Seed -> K -> N),
    (forall key, eqb key key = true) ->
    forall seed key (first second : A),
      elements (of_list eqb hash seed [(key, first); (key, second)]) =
      [(key, first)].
Proof.
  intros K Seed A eqb hash Heqb seed key first second.
  rewrite of_list_first_wins_same_key by exact Heqb.
  apply bindings_singleton.
Qed.

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
