(** Source model for the future compact-array backend.

    [pseq] intentionally exposes only a logical list view in Rocq.  H4's
    target array adapter must refine these operations by allocating a fresh
    private array for every update; it is not yet an OCaml heap proof. *)

From Stdlib Require Import List NArith.
Import ListNotations.

Require Import HashTable HashTableBits HashTableBucket.

Set Implicit Arguments.

Record pseq (A : Type) : Type := {
  pseq_view : list A
}.

Arguments pseq_view {A} _.

Definition pseq_empty {A : Type} : pseq A := {| pseq_view := [] |}.
Definition pseq_of_list {A : Type} (items : list A) : pseq A :=
  {| pseq_view := items |}.
Definition pseq_get {A : Type} (index : nat) (items : pseq A) : option A :=
  nth_error (pseq_view items) index.
Definition pseq_insert {A : Type} (index : nat) (item : A) (items : pseq A)
    : pseq A :=
  pseq_of_list (dense_insert index item (pseq_view items)).
Definition pseq_replace {A : Type} (index : nat) (item : A) (items : pseq A)
    : pseq A :=
  pseq_of_list (dense_replace index item (pseq_view items)).
Definition pseq_remove {A : Type} (index : nat) (items : pseq A) : pseq A :=
  pseq_of_list (dense_remove index (pseq_view items)).

Lemma pseq_empty_view :
  forall A, @pseq_view A pseq_empty = [].
Proof. reflexivity. Qed.

Lemma pseq_get_view :
  forall A index (items : pseq A),
    pseq_get index items = nth_error (pseq_view items) index.
Proof. reflexivity. Qed.

Lemma pseq_insert_view :
  forall A index (item : A) items,
    pseq_view (pseq_insert index item items) =
    dense_insert index item (pseq_view items).
Proof. reflexivity. Qed.

Lemma pseq_replace_view :
  forall A index (item : A) items,
    pseq_view (pseq_replace index item items) =
    dense_replace index item (pseq_view items).
Proof. reflexivity. Qed.

Lemma pseq_remove_view :
  forall A index (items : pseq A),
    pseq_view (pseq_remove index items) = dense_remove index (pseq_view items).
Proof. reflexivity. Qed.

Lemma pseq_get_insert_same :
  forall A index (item : A) items,
    index <= length (pseq_view items) ->
    pseq_get index (pseq_insert index item items) = Some item.
Proof.
  intros A index item items Hbound.
  unfold pseq_get, pseq_insert, pseq_of_list.
  now apply dense_get_insert_same.
Qed.

Lemma pseq_get_insert_before :
  forall A index before (item : A) items,
    before < index ->
    index <= length (pseq_view items) ->
    pseq_get before (pseq_insert index item items) = pseq_get before items.
Proof.
  intros A index before item items Hbefore Hbound.
  unfold pseq_get, pseq_insert, pseq_of_list.
  now apply dense_get_insert_before.
Qed.

Lemma pseq_get_insert_after :
  forall A index after (item : A) items,
    index <= after ->
    index <= length (pseq_view items) ->
    pseq_get (S after) (pseq_insert index item items) = pseq_get after items.
Proof.
  intros A index after item items Hafter Hbound.
  unfold pseq_get, pseq_insert, pseq_of_list.
  now apply dense_get_insert_after.
Qed.

Lemma pseq_get_replace_same :
  forall A index (item : A) items,
    index < length (pseq_view items) ->
    pseq_get index (pseq_replace index item items) = Some item.
Proof.
  intros A index item items Hbound.
  unfold pseq_get, pseq_replace, pseq_of_list.
  now apply dense_get_replace_same.
Qed.

Lemma pseq_get_replace_other :
  forall A index other (item : A) items,
    other <> index ->
    pseq_get other (pseq_replace index item items) = pseq_get other items.
Proof.
  intros A index other item items Hother.
  unfold pseq_get, pseq_replace, pseq_of_list.
  now apply dense_get_replace_other.
Qed.

Lemma pseq_get_remove_before :
  forall A index before (items : pseq A),
    before < index ->
    pseq_get before (pseq_remove index items) = pseq_get before items.
Proof.
  intros A index before items Hbefore.
  unfold pseq_get, pseq_remove, pseq_of_list.
  now apply dense_get_remove_before.
Qed.

Lemma pseq_get_remove_after :
  forall A index after (items : pseq A),
    index <= after ->
    pseq_get after (pseq_remove index items) = pseq_get (S after) items.
Proof.
  intros A index after items Hafter.
  unfold pseq_get, pseq_remove, pseq_of_list.
  now apply dense_get_remove_after.
Qed.

Lemma pseq_insert_length :
  forall A index (item : A) items,
    length (pseq_view (pseq_insert index item items)) = S (length (pseq_view items)).
Proof.
  intros A index item items.
  rewrite pseq_insert_view. apply dense_insert_length.
Qed.

Lemma pseq_replace_length :
  forall A index (item : A) items,
    length (pseq_view (pseq_replace index item items)) = length (pseq_view items).
Proof.
  intros A index item items.
  rewrite pseq_replace_view. apply dense_replace_length.
Qed.

Lemma pseq_remove_length_le :
  forall A index (items : pseq A),
    length (pseq_view (pseq_remove index items)) <= length (pseq_view items).
Proof.
  intros A index items.
  rewrite pseq_remove_view. apply dense_remove_length_le.
Qed.

Lemma pseq_remove_length_hit :
  forall A index (items : pseq A),
    index < length (pseq_view items) ->
    length (pseq_view (pseq_remove index items)) = Nat.pred (length (pseq_view items)).
Proof.
  intros A index items Hbound.
  rewrite pseq_remove_view. now apply dense_remove_length_hit.
Qed.

Inductive native_tree (K A : Type) : Type :=
| NativeEmpty
| NativeLeaf (full_hash : N) (key : K) (value : A)
| NativeCollision (full_hash : N) (entries : pseq (K * A))
| NativeBranch (bitmap : N) (children : pseq (native_tree K A)).

Arguments NativeEmpty {K A}.
Arguments NativeLeaf {K A} _ _ _.
Arguments NativeCollision {K A} _ _.
Arguments NativeBranch {K A} _ _.

Fixpoint source_of_native {K A : Type} (native : native_tree K A) : tree K A :=
  match native with
  | NativeEmpty => Empty
  | NativeLeaf full_hash key value => Leaf full_hash key value
  | NativeCollision full_hash entries => Collision full_hash (pseq_view entries)
  | NativeBranch bitmap children =>
      Branch bitmap (map source_of_native (pseq_view children))
  end.

Fixpoint native_of_source {K A : Type} (source : tree K A) : native_tree K A :=
  match source with
  | Empty => NativeEmpty
  | Leaf full_hash key value => NativeLeaf full_hash key value
  | Collision full_hash entries => NativeCollision full_hash (pseq_of_list entries)
  | Branch bitmap children =>
      NativeBranch bitmap (pseq_of_list (map native_of_source children))
  end.

Definition native_refines {K A : Type} (native : native_tree K A)
    (source : tree K A) : Prop := source_of_native native = source.

Lemma native_empty_refines :
  forall K A, @native_refines K A NativeEmpty Empty.
Proof. reflexivity. Qed.

Lemma native_leaf_refines :
  forall K A full_hash (key : K) (value : A),
    native_refines (NativeLeaf full_hash key value) (Leaf full_hash key value).
Proof. reflexivity. Qed.

Lemma native_collision_refines :
  forall K A full_hash (entries : list (K * A)),
    native_refines (NativeCollision full_hash (pseq_of_list entries))
                   (Collision full_hash entries).
Proof. reflexivity. Qed.

Lemma source_of_native_of_source :
  forall K A (source : tree K A),
    source_of_native (native_of_source source) = source.
Proof.
  intros K A source.
  assert (Hroundtrip : forall (source' : tree K A),
    source_of_native (native_of_source source') = source').
  { fix source_roundtrip 1.
    intro source'. destruct source' as [|full_hash key value|full_hash entries|bitmap children].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. f_equal.
      induction children as [|child children IH].
      + reflexivity.
      + cbn. rewrite (source_roundtrip child), IH.
        reflexivity. }
  apply Hroundtrip.
Qed.

Lemma pseq_get_source_children :
  forall K A index (children : pseq (native_tree K A)) child,
    pseq_get index children = Some child ->
    dense_get index (map source_of_native (pseq_view children)) =
    Some (source_of_native child).
Proof.
  intros K A index children child Hget.
  unfold pseq_get, dense_get in *.
  rewrite nth_error_map, Hget. reflexivity.
Qed.

Lemma pseq_get_source_children_none :
  forall K A index (children : pseq (native_tree K A)),
    pseq_get index children = None ->
    dense_get index (map source_of_native (pseq_view children)) = None.
Proof.
  intros K A index children Hget.
  unfold pseq_get, dense_get in *.
  rewrite nth_error_map, Hget. reflexivity.
Qed.

Definition native_branch_replace {K A : Type} (bitmap slot : N)
    (child : native_tree K A) (children : pseq (native_tree K A)) : native_tree K A :=
  NativeBranch bitmap (pseq_replace (rank bitmap slot) child children).

Definition native_branch_insert {K A : Type} (bitmap slot : N)
    (child : native_tree K A) (children : pseq (native_tree K A)) : native_tree K A :=
  NativeBranch (N.lor bitmap (bitmap_bit slot))
    (pseq_insert (rank bitmap slot) child children).

(** Lookup is a recursive compact-child worker.  Update and removal remain
    source-refined while their compact workers are developed. *)
Fixpoint native_get {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (native : native_tree K A)
    : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if N.eqb full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if N.eqb full_hash stored_hash then bucket_get eqb key (pseq_view entries)
      else None
  | NativeBranch bitmap children =>
      match fuel with
      | O => None
      | S fuel' =>
          let slot := chunk full_hash depth in
          if bitmap_has bitmap slot then
            match pseq_get (rank bitmap slot) children with
            | Some child => native_get eqb fuel' (S depth) full_hash key child
            | None => None
            end
          else None
      end
  end.

Definition native_set {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (value : A)
    (native : native_tree K A) : native_tree K A :=
  native_of_source (set_tree eqb fuel depth full_hash key value (source_of_native native)).

Definition native_remove {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (native : native_tree K A)
    : native_tree K A :=
  native_of_source (remove_tree eqb fuel depth full_hash key (source_of_native native)).

Lemma native_get_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A),
    native_get eqb fuel depth full_hash key native =
    get_tree eqb fuel depth full_hash key (source_of_native native).
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key native;
    destruct native as [|stored_hash stored value|stored_hash entries|bitmap children];
    cbn [native_get source_of_native get_tree].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent; auto.
    destruct (pseq_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild.
    + cbn [source_of_native get_tree].
      rewrite (@pseq_get_source_children K A
        (rank bitmap (chunk full_hash depth)) children child Hchild).
      now apply IH.
    + cbn [source_of_native get_tree].
      rewrite (@pseq_get_source_children_none K A
        (rank bitmap (chunk full_hash depth)) children Hchild).
      reflexivity.
Qed.

Lemma native_set_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         (native : native_tree K A),
    source_of_native (native_set eqb fuel depth full_hash key value native) =
    set_tree eqb fuel depth full_hash key value (source_of_native native).
Proof. intros. unfold native_set. apply source_of_native_of_source. Qed.

Lemma native_remove_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A),
    source_of_native (native_remove eqb fuel depth full_hash key native) =
    remove_tree eqb fuel depth full_hash key (source_of_native native).
Proof. intros. unfold native_remove. apply source_of_native_of_source. Qed.

Record native_table (K Seed A : Type) : Type := {
  native_table_seed : Seed;
  native_table_root : native_tree K A
}.

Definition source_table_of_native {K Seed A : Type}
    (native : native_table K Seed A) : table K Seed A :=
  {| table_seed := native_table_seed native;
     table_root := source_of_native (native_table_root native) |}.

Definition native_empty {K Seed A : Type} (seed : Seed) : native_table K Seed A :=
  {| native_table_seed := seed; native_table_root := NativeEmpty |}.

Definition native_table_set {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (key : K) (value : A)
    (native : native_table K Seed A) : native_table K Seed A :=
  {| native_table_seed := native_table_seed native;
     native_table_root := native_set eqb branch_levels 0
       (hash (native_table_seed native) key) key value (native_table_root native) |}.

Definition native_table_remove {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (key : K)
    (native : native_table K Seed A) : native_table K Seed A :=
  {| native_table_seed := native_table_seed native;
     native_table_root := native_remove eqb branch_levels 0
       (hash (native_table_seed native) key) key (native_table_root native) |}.

Definition native_table_get {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (key : K) (native : native_table K Seed A)
    : option A :=
  native_get eqb branch_levels 0 (hash (native_table_seed native) key) key
    (native_table_root native).

Definition native_table_mem {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (key : K) (native : native_table K Seed A) : bool :=
  match native_table_get eqb hash key native with
  | Some _ => true
  | None => false
  end.

Definition native_table_elements {K Seed A : Type}
    (native : native_table K Seed A) : list (K * A) :=
  elements (source_table_of_native native).

Definition native_table_is_empty {K Seed A : Type}
    (native : native_table K Seed A) : bool :=
  match native_table_root native with
  | NativeEmpty => true
  | _ => false
  end.

Lemma source_table_native_empty :
  forall K Seed A (seed : Seed),
    @source_table_of_native K Seed A (native_empty seed) = empty seed.
Proof. reflexivity. Qed.

Lemma native_table_set_seed :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (value : A) (native : native_table K Seed A),
    native_table_seed (native_table_set eqb hash key value native) =
    native_table_seed native.
Proof. reflexivity. Qed.

Lemma native_table_remove_seed :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (native : native_table K Seed A),
    native_table_seed (native_table_remove eqb hash key native) =
    native_table_seed native.
Proof. reflexivity. Qed.

Lemma source_table_native_set :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (value : A) (native : native_table K Seed A),
    source_table_of_native (native_table_set eqb hash key value native) =
    set eqb hash key value (source_table_of_native native).
Proof.
  intros K Seed A eqb hash key value [seed root].
  unfold source_table_of_native, native_table_set, set.
  f_equal. apply native_set_refines.
Qed.

Lemma source_table_native_remove :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (native : native_table K Seed A),
    source_table_of_native (native_table_remove eqb hash key native) =
    remove eqb hash key (source_table_of_native native).
Proof.
  intros K Seed A eqb hash key [seed root].
  unfold source_table_of_native, native_table_remove, remove.
  f_equal. apply native_remove_refines.
Qed.

Lemma native_table_get_refines :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (native : native_table K Seed A),
    native_table_get eqb hash key native =
    get eqb hash key (source_table_of_native native).
Proof.
  intros K Seed A eqb hash key [seed root].
  exact (@native_get_refines K A eqb branch_levels 0 (hash seed key) key root).
Qed.

Lemma native_table_mem_refines :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         key (native : native_table K Seed A),
    native_table_mem eqb hash key native =
    mem eqb hash key (source_table_of_native native).
Proof.
  intros K Seed A eqb hash key native.
  unfold native_table_mem, mem.
  now rewrite native_table_get_refines.
Qed.

Lemma native_table_elements_refines :
  forall K Seed A (native : native_table K Seed A),
    native_table_elements native = elements (source_table_of_native native).
Proof. reflexivity. Qed.

Lemma native_table_is_empty_refines :
  forall K Seed A (native : native_table K Seed A),
    native_table_is_empty native = is_empty (source_table_of_native native).
Proof. intros K Seed A [seed root]; destruct root; reflexivity. Qed.
