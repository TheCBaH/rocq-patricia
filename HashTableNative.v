(** Source model for the future compact-array backend.

    [pseq] intentionally exposes only a logical list view in Rocq.  H4's
    target array adapter must refine these operations by allocating a fresh
    private array for every update; it is not yet an OCaml heap proof. *)

From Stdlib Require Import List NArith.
Import ListNotations.

Require Import HashTable HashTableBits HashTableBucket HashTableNativeBits.

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
Definition pseq_length {A : Type} (items : pseq A) : nat :=
  length (pseq_view items).
Definition pseq_is_empty {A : Type} (items : pseq A) : bool :=
  match pseq_view items with [] => true | _ => false end.
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

Lemma pseq_length_view :
  forall A (items : pseq A), pseq_length items = length (pseq_view items).
Proof. reflexivity. Qed.

Lemma pseq_is_empty_spec :
  forall A (items : pseq A),
    pseq_is_empty items = true <-> pseq_view items = [].
Proof.
  intros A [items]. destruct items; simpl; split; intro H; try reflexivity; discriminate.
Qed.

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

Definition native_branch_replace_at {K A : Type} (bitmap : N) (index : nat)
    (child : native_tree K A) (children : pseq (native_tree K A)) : native_tree K A :=
  NativeBranch bitmap (pseq_replace index child children).

Definition native_branch_replace {K A : Type} (bitmap slot : N)
    (child : native_tree K A) (children : pseq (native_tree K A)) : native_tree K A :=
  native_branch_replace_at bitmap (native_rank bitmap slot) child children.

Definition native_branch_insert_at {K A : Type} (bitmap slot : N) (index : nat)
    (child : native_tree K A) (children : pseq (native_tree K A)) : native_tree K A :=
  NativeBranch (native_bitmap_insert bitmap slot)
    (pseq_insert index child children).

Definition native_branch_insert {K A : Type} (bitmap slot : N)
    (child : native_tree K A) (children : pseq (native_tree K A)) : native_tree K A :=
  native_branch_insert_at bitmap slot (native_rank bitmap slot) child children.

Lemma native_branch_replace_bitmap_bound :
  forall K A (bitmap slot : N) (child : native_tree K A)
         (children : pseq (native_tree K A)),
    (bitmap < bitmap_limit)%N ->
    match native_branch_replace bitmap slot child children with
    | NativeBranch bitmap' _ => (bitmap' < bitmap_limit)%N
    | _ => False
    end.
Proof.
  intros K A bitmap slot child children Hbound.
  unfold native_branch_replace. exact Hbound.
Qed.

Lemma native_branch_insert_bitmap_bound :
  forall K A (bitmap slot : N) (child : native_tree K A)
         (children : pseq (native_tree K A)),
    (bitmap < bitmap_limit)%N ->
    (slot < branch_width)%N ->
    bitmap_has bitmap slot = false ->
    match native_branch_insert bitmap slot child children with
    | NativeBranch bitmap' _ => (bitmap' < bitmap_limit)%N
    | _ => False
    end.
Proof.
  intros K A bitmap slot child children Hbound Hslot Habsent.
  unfold native_branch_insert. cbn.
  apply bitmap_lor_bit_bound_absent; assumption.
Qed.

Lemma map_dense_insert :
  forall A B (f : A -> B) index (item : A) items,
    map f (dense_insert index item items) =
    dense_insert index (f item) (map f items).
Proof.
  intros A B f index.
  induction index as [|index IH]; intros item items;
    destruct items as [|head tail]; cbn; auto.
  now rewrite IH.
Qed.

Lemma map_dense_replace :
  forall A B (f : A -> B) index (item : A) items,
    map f (dense_replace index item items) =
    dense_replace index (f item) (map f items).
Proof.
  intros A B f index.
  induction index as [|index IH]; intros item items;
    destruct items as [|head tail]; cbn; auto.
  now rewrite IH.
Qed.

Lemma map_dense_remove :
  forall A B (f : A -> B) index items,
    map f (dense_remove index items) =
    dense_remove index (map f items).
Proof.
  intros A B f index.
  induction index as [|index IH]; intros items;
    destruct items as [|head tail]; cbn; auto.
  now rewrite IH.
Qed.

Lemma source_of_native_branch_insert :
  forall K A (bitmap slot : N) (child : native_tree K A)
         (children : pseq (native_tree K A)),
    source_of_native (native_branch_insert bitmap slot child children) =
    branch_insert bitmap slot (source_of_native child)
      (map source_of_native (pseq_view children)).
Proof.
  intros K A bitmap slot child children.
  unfold native_branch_insert, source_of_native, pseq_insert, pseq_of_list,
    branch_insert.
  cbn. f_equal. apply map_dense_insert.
Qed.

Lemma source_of_native_branch_insert_at :
  forall K A (bitmap slot : N) index (child : native_tree K A)
         (children : pseq (native_tree K A)),
    source_of_native (native_branch_insert_at bitmap slot index child children) =
    Branch (N.lor bitmap (bitmap_bit slot))
      (dense_insert index (source_of_native child)
        (map source_of_native (pseq_view children))).
Proof.
  intros K A bitmap slot index child children.
  unfold native_branch_insert_at, source_of_native, pseq_insert, pseq_of_list.
  cbn. f_equal. apply map_dense_insert.
Qed.

Lemma source_of_native_branch_replace :
  forall K A (bitmap slot : N) (child : native_tree K A)
         (children : pseq (native_tree K A)),
    source_of_native (native_branch_replace bitmap slot child children) =
    branch_replace bitmap slot (source_of_native child)
      (map source_of_native (pseq_view children)).
Proof.
  intros K A bitmap slot child children.
  unfold native_branch_replace, source_of_native, pseq_replace, pseq_of_list,
    branch_replace.
  cbn. f_equal. apply map_dense_replace.
Qed.

Lemma source_of_native_branch_replace_at :
  forall K A (bitmap : N) index (child : native_tree K A)
         (children : pseq (native_tree K A)),
    source_of_native (native_branch_replace_at bitmap index child children) =
    Branch bitmap (dense_replace index (source_of_native child)
      (map source_of_native (pseq_view children))).
Proof.
  intros K A bitmap index child children.
  unfold native_branch_replace_at, source_of_native, pseq_replace, pseq_of_list.
  cbn. f_equal. apply map_dense_replace.
Qed.

Definition native_children_remove {K A : Type} (bitmap slot : N) (index : nat)
    (children : pseq (native_tree K A)) : native_tree K A :=
  let children' := pseq_remove index children in
  if pseq_is_empty children' then NativeEmpty
  else NativeBranch (native_bitmap_remove bitmap slot) children'.

Definition native_branch_remove_at {K A : Type} (bitmap slot : N) (index : nat)
    (children : pseq (native_tree K A)) : native_tree K A :=
  native_children_remove bitmap slot index children.

Definition native_branch_remove {K A : Type} (bitmap slot : N)
    (children : pseq (native_tree K A)) : native_tree K A :=
  native_branch_remove_at bitmap slot (native_rank bitmap slot) children.

Lemma native_children_remove_bitmap_bound :
  forall K A (bitmap slot : N) index (children : pseq (native_tree K A)),
    (bitmap < bitmap_limit)%N ->
    match native_children_remove bitmap slot index children with
    | NativeEmpty => True
    | NativeBranch bitmap' _ => (bitmap' < bitmap_limit)%N
    | _ => False
    end.
Proof.
  intros K A bitmap slot index children Hbound.
  unfold native_children_remove, pseq_remove, pseq_of_list, pseq_is_empty.
  destruct (dense_remove index (pseq_view children)) as [|child tail]; cbn.
  - exact I.
  - apply bitmap_ldiff_bit_bound. exact Hbound.
Qed.

Lemma native_branch_remove_bitmap_bound :
  forall K A (bitmap slot : N) (children : pseq (native_tree K A)),
    (bitmap < bitmap_limit)%N ->
    match native_branch_remove bitmap slot children with
    | NativeEmpty => True
    | NativeBranch bitmap' _ => (bitmap' < bitmap_limit)%N
    | _ => False
    end.
Proof.
  intros K A bitmap slot children Hbound.
  unfold native_branch_remove.
  eapply native_children_remove_bitmap_bound; eauto.
Qed.

Lemma source_of_native_children_remove :
  forall K A (bitmap slot : N) index (children : pseq (native_tree K A)),
    source_of_native (native_children_remove bitmap slot index children) =
    match dense_remove index (map source_of_native (pseq_view children)) with
    | [] => Empty
    | _ => Branch (N.ldiff bitmap (bitmap_bit slot))
        (dense_remove index (map source_of_native (pseq_view children)))
    end.
Proof.
  intros K A bitmap slot index children.
  unfold native_children_remove, pseq_remove, pseq_of_list, pseq_is_empty, source_of_native.
  rewrite <- map_dense_remove.
  destruct (dense_remove index (pseq_view children)) as [|head tail]; reflexivity.
Qed.

Lemma source_of_native_branch_remove :
  forall K A (bitmap slot : N) (children : pseq (native_tree K A)),
    source_of_native (native_branch_remove bitmap slot children) =
    branch_remove bitmap slot (map source_of_native (pseq_view children)).
Proof.
  intros K A bitmap slot children.
  unfold native_branch_remove, branch_remove.
  apply source_of_native_children_remove.
Qed.

Lemma source_of_native_branch_remove_at :
  forall K A (bitmap slot : N) index (children : pseq (native_tree K A)),
    source_of_native (native_branch_remove_at bitmap slot index children) =
    match dense_remove index (map source_of_native (pseq_view children)) with
    | [] => Empty
    | _ => Branch (N.ldiff bitmap (bitmap_bit slot))
        (dense_remove index (map source_of_native (pseq_view children)))
    end.
Proof.
  intros K A bitmap slot index children.
  unfold native_branch_remove_at. apply source_of_native_children_remove.
Qed.

(** Lookup, update and removal are recursive compact-child workers. *)
Definition native_join_two {K A : Type} (left_hash : N) (left : native_tree K A)
    (right_hash : N) (right : native_tree K A) (depth : nat) : native_tree K A :=
  let left_slot := native_chunk left_hash depth in
  let right_slot := native_chunk right_hash depth in
  let bitmap := native_bitmap_insert (native_bitmap_bit left_slot) right_slot in
  if native_slot_lt left_slot right_slot
  then NativeBranch bitmap (pseq_of_list [left; right])
  else NativeBranch bitmap (pseq_of_list [right; left]).

Lemma native_join_two_refines :
  forall K A depth left_hash right_hash (left right : native_tree K A),
    source_of_native (native_join_two left_hash left right_hash right depth) =
    join_two left_hash (source_of_native left)
      right_hash (source_of_native right) depth.
Proof.
  intros K A depth left_hash right_hash left right.
  unfold native_join_two, join_two, native_slot_lt, native_chunk, native_bitmap_bit,
    native_bitmap_insert.
  cbn [source_of_native pseq_of_list].
  destruct (N.ltb (chunk left_hash depth) (chunk right_hash depth)); reflexivity.
Qed.

Fixpoint native_join_worker {K A : Type} (fuel depth : nat)
    (left_hash : N) (left : native_tree K A)
    (right_hash : N) (right : native_tree K A) : native_tree K A :=
  match fuel with
  | O => native_join_two left_hash left right_hash right depth
  | S fuel' =>
      if native_bounded_eq (native_chunk left_hash depth) (native_chunk right_hash depth)
      then NativeBranch (native_bitmap_bit (native_chunk left_hash depth))
             (pseq_of_list [native_join_worker fuel' (S depth)
               left_hash left right_hash right])
      else native_join_two left_hash left right_hash right depth
  end.

Lemma native_join_worker_refines :
  forall K A fuel depth left_hash right_hash (left right : native_tree K A),
    source_of_native (native_join_worker fuel depth left_hash left right_hash right) =
    join_worker fuel depth left_hash (source_of_native left)
      right_hash (source_of_native right).
Proof.
  intros K A fuel.
  induction fuel as [|fuel IH]; intros depth left_hash right_hash left right.
  - cbn [native_join_worker join_worker]. apply native_join_two_refines.
  - cbn [native_join_worker join_worker].
    unfold native_bounded_eq.
    destruct (N.eqb (chunk left_hash depth) (chunk right_hash depth)) eqn:Hslots.
    + change (N.eqb (native_chunk left_hash depth)
        (native_chunk right_hash depth) = true) in Hslots.
      rewrite Hslots.
      change (Branch (bitmap_bit (chunk left_hash depth))
        [source_of_native (native_join_worker fuel (S depth)
          left_hash left right_hash right)] =
        Branch (bitmap_bit (chunk left_hash depth))
          [join_worker fuel (S depth) left_hash (source_of_native left)
            right_hash (source_of_native right)]).
      f_equal. f_equal. apply IH.
    + change (N.eqb (native_chunk left_hash depth)
        (native_chunk right_hash depth) = false) in Hslots.
      rewrite Hslots. apply native_join_two_refines.
Qed.

Definition native_leaf_set {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (value : A)
    (stored_hash : N) (stored : K) (old : A) : native_tree K A :=
  if eqb key stored then NativeLeaf stored_hash stored value
  else if native_bounded_eq full_hash stored_hash
       then NativeCollision stored_hash
         (pseq_of_list [(stored, old); (key, value)])
       else native_join_worker fuel depth full_hash
         (NativeLeaf full_hash key value) stored_hash (NativeLeaf stored_hash stored old).

Lemma native_leaf_set_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         stored_hash stored (old : A),
    source_of_native
      (native_leaf_set eqb fuel depth full_hash key value stored_hash stored old) =
    set_tree eqb fuel depth full_hash key value (Leaf stored_hash stored old).
Proof.
  intros K A eqb fuel depth full_hash key value stored_hash stored old.
  unfold native_leaf_set, native_bounded_eq.
  rewrite set_tree_leaf.
  destruct (eqb key stored) eqn:Hkey.
  - reflexivity.
  - destruct (N.eqb full_hash stored_hash) eqn:Hhash.
    + reflexivity.
    + apply native_join_worker_refines.
Qed.

Definition native_leaf_remove {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (stored_hash : N) (stored : K) (value : A)
    : native_tree K A :=
  if native_bounded_eq full_hash stored_hash then
    if eqb key stored then NativeEmpty else NativeLeaf stored_hash stored value
  else NativeLeaf stored_hash stored value.

Lemma native_leaf_remove_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         stored_hash stored (value : A),
    source_of_native
      (native_leaf_remove eqb full_hash key stored_hash stored value) =
    remove_tree eqb fuel depth full_hash key (Leaf stored_hash stored value).
Proof.
  intros K A eqb fuel depth full_hash key stored_hash stored value.
  unfold native_leaf_remove, native_bounded_eq.
  rewrite remove_tree_leaf.
  destruct (N.eqb full_hash stored_hash) eqn:Hhash.
  - destruct (eqb key stored) eqn:Hkey; reflexivity.
  - reflexivity.
Qed.

Fixpoint native_bucket_get {K A : Type} (eqb : K -> K -> bool) (query : K)
    (entries : pseq (K * A)) (index remaining : nat) : option A :=
  match remaining with
  | O => None
  | S remaining' =>
      match pseq_get index entries with
      | None => None
      | Some (stored, value) =>
          if eqb query stored then Some value
          else native_bucket_get eqb query entries (S index) remaining'
      end
  end.

Lemma native_bucket_get_refines :
  forall K A (eqb : K -> K -> bool) (query : K)
         (entries : pseq (K * A)) index remaining,
    native_bucket_get eqb query entries index remaining =
    bucket_get_index eqb query (pseq_view entries) index remaining.
Proof.
  intros K A eqb query entries index remaining.
  revert index.
  induction remaining as [|remaining IH]; intro index.
  - reflexivity.
  - cbn [native_bucket_get bucket_get_index].
    rewrite pseq_get_view.
    destruct (nth_error (pseq_view entries) index) as [[stored value]|].
    + destruct (eqb query stored); [reflexivity|apply IH].
    + reflexivity.
Qed.

Fixpoint native_bucket_set {K A : Type} (eqb : K -> K -> bool)
    (key : K) (value : A) (entries : pseq (K * A))
    (index remaining : nat) : pseq (K * A) :=
  match remaining with
  | O => pseq_insert index (key, value) entries
  | S remaining' =>
      match pseq_get index entries with
      | None => pseq_insert index (key, value) entries
      | Some (stored, old_value) =>
          if eqb key stored then pseq_replace index (stored, value) entries
          else native_bucket_set eqb key value entries (S index) remaining'
      end
  end.

Lemma native_bucket_set_refines :
  forall K A (eqb : K -> K -> bool) (key : K) (value : A)
         (entries : pseq (K * A)) index remaining,
    pseq_view (native_bucket_set eqb key value entries index remaining) =
    bucket_set_index eqb key value (pseq_view entries) index remaining.
Proof.
  intros K A eqb key value entries index remaining.
  revert index.
  induction remaining as [|remaining IH]; intro index.
  - reflexivity.
  - cbn [native_bucket_set bucket_set_index].
    rewrite pseq_get_view.
    destruct (nth_error (pseq_view entries) index) as [[stored old_value]|].
    + destruct (eqb key stored); [apply pseq_replace_view|apply IH].
    + apply pseq_insert_view.
Qed.

(** Normalize an updated collision without converting its sequence to a list.
    The length/get operations remain checked and total for raw modeled trees. *)
Definition native_normalize_collision {K A : Type} (full_hash : N)
    (entries : pseq (K * A)) : native_tree K A :=
  match pseq_length entries with
  | O => NativeEmpty
  | S O =>
      match pseq_get O entries with
      | Some (key, value) => NativeLeaf full_hash key value
      | None => NativeEmpty
      end
  | S (S _) => NativeCollision full_hash entries
  end.

Lemma native_normalize_collision_refines :
  forall K A (full_hash : N) (entries : pseq (K * A)),
    source_of_native (native_normalize_collision full_hash entries) =
    normalize_collision full_hash (pseq_view entries).
Proof.
  intros K A full_hash [entries].
  destruct entries as [|[key value] [|[key' value'] entries]]; reflexivity.
Qed.

Definition native_collision_set {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (value : A)
    (stored_hash : N) (entries : pseq (K * A)) : native_tree K A :=
  if native_bounded_eq full_hash stored_hash then
    native_normalize_collision stored_hash
      (native_bucket_set eqb key value entries O (pseq_length entries))
  else native_join_worker fuel depth full_hash
    (NativeLeaf full_hash key value) stored_hash (NativeCollision stored_hash entries).

Lemma native_collision_set_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         stored_hash (entries : pseq (K * A)),
    source_of_native
      (native_collision_set eqb fuel depth full_hash key value stored_hash entries) =
    set_tree eqb fuel depth full_hash key value
      (Collision stored_hash (pseq_view entries)).
Proof.
  intros K A eqb fuel depth full_hash key value stored_hash entries.
  unfold native_collision_set, native_bounded_eq.
  destruct (N.eqb full_hash stored_hash) eqn:Hhash.
  - rewrite set_tree_collision, Hhash.
    rewrite native_normalize_collision_refines.
    rewrite native_bucket_set_refines, pseq_length_view, bucket_set_index_spec.
    reflexivity.
  - rewrite set_tree_collision, Hhash.
    apply native_join_worker_refines.
Qed.

Fixpoint native_bucket_remove {K A : Type} (eqb : K -> K -> bool)
    (key : K) (entries : pseq (K * A))
    (index remaining : nat) : pseq (K * A) :=
  match remaining with
  | O => entries
  | S remaining' =>
      match pseq_get index entries with
      | None => entries
      | Some (stored, value) =>
          if eqb key stored then pseq_remove index entries
          else native_bucket_remove eqb key entries (S index) remaining'
      end
  end.

Lemma native_bucket_remove_refines :
  forall K A (eqb : K -> K -> bool) (key : K)
         (entries : pseq (K * A)) index remaining,
    pseq_view (native_bucket_remove eqb key entries index remaining) =
    bucket_remove_index eqb key (pseq_view entries) index remaining.
Proof.
  intros K A eqb key entries index remaining.
  revert index.
  induction remaining as [|remaining IH]; intro index.
  - reflexivity.
  - cbn [native_bucket_remove bucket_remove_index].
    rewrite pseq_get_view.
    destruct (nth_error (pseq_view entries) index) as [[stored value]|].
    + destruct (eqb key stored); [apply pseq_remove_view|apply IH].
    + reflexivity.
Qed.

Definition native_collision_remove {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (stored_hash : N) (entries : pseq (K * A))
    : native_tree K A :=
  if native_bounded_eq full_hash stored_hash then
    native_normalize_collision stored_hash
      (native_bucket_remove eqb key entries O (pseq_length entries))
  else NativeCollision stored_hash entries.

Lemma native_collision_remove_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         stored_hash (entries : pseq (K * A)),
    source_of_native
      (native_collision_remove eqb full_hash key stored_hash entries) =
    remove_tree eqb fuel depth full_hash key
      (Collision stored_hash (pseq_view entries)).
Proof.
  intros K A eqb fuel depth full_hash key stored_hash entries.
  unfold native_collision_remove, native_bounded_eq.
  destruct (N.eqb full_hash stored_hash) eqn:Hhash.
  - rewrite remove_tree_collision, Hhash.
    rewrite native_normalize_collision_refines.
    rewrite native_bucket_remove_refines, pseq_length_view, bucket_remove_index_spec.
    reflexivity.
  - rewrite remove_tree_collision, Hhash.
    reflexivity.
Qed.

Fixpoint native_get {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (native : native_tree K A)
    : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      match fuel with
      | O => None
      | S fuel' =>
          let slot := native_chunk full_hash depth in
          if native_bitmap_has bitmap slot then
            match pseq_get (native_rank bitmap slot) children with
            | Some child => native_get eqb fuel' (S depth) full_hash key child
            | None => None
            end
          else None
      end
  end.

Fixpoint native_set {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (value : A)
    (native : native_tree K A) : native_tree K A :=
  match native, fuel with
  | NativeBranch bitmap children, S fuel' =>
      let slot := native_chunk full_hash depth in
      let index := native_rank bitmap slot in
      if native_bitmap_has bitmap slot then
        match pseq_get index children with
        | Some child => native_branch_replace_at bitmap index
            (native_set eqb fuel' (S depth) full_hash key value child) children
        | None => native_branch_insert_at bitmap slot index
            (NativeLeaf full_hash key value) children
        end
      else native_branch_insert_at bitmap slot index (NativeLeaf full_hash key value) children
  | NativeEmpty, _ => NativeLeaf full_hash key value
  | NativeLeaf stored_hash stored old, _ =>
      native_leaf_set eqb fuel depth full_hash key value stored_hash stored old
  | NativeCollision stored_hash entries, _ =>
      native_collision_set eqb fuel depth full_hash key value stored_hash entries
  | NativeBranch bitmap children, O => NativeBranch bitmap children
  end.

Fixpoint native_remove {K A : Type} (eqb : K -> K -> bool)
    (fuel depth : nat) (full_hash : N) (key : K) (native : native_tree K A)
    : native_tree K A :=
  match native, fuel with
  | NativeBranch bitmap children, S fuel' =>
      let slot := native_chunk full_hash depth in
      let index := native_rank bitmap slot in
      if native_bitmap_has bitmap slot then
        match pseq_get index children with
        | Some child =>
            match native_remove eqb fuel' (S depth) full_hash key child with
            | NativeEmpty => native_branch_remove_at bitmap slot index children
            | child' => native_branch_replace_at bitmap index child' children
            end
        | None => NativeBranch bitmap children
        end
      else NativeBranch bitmap children
  | NativeEmpty, _ => NativeEmpty
  | NativeLeaf stored_hash stored value, _ =>
      native_leaf_remove eqb full_hash key stored_hash stored value
  | NativeCollision stored_hash entries, _ =>
      native_collision_remove eqb full_hash key stored_hash entries
  | NativeBranch bitmap children, O => NativeBranch bitmap children
  end.

Lemma native_get_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A),
    native_get eqb fuel depth full_hash key native =
    get_tree eqb fuel depth full_hash key (source_of_native native).
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key native;
    destruct native as [|stored_hash stored value|stored_hash entries|bitmap children];
    cbn [native_get native_bounded_eq native_chunk native_bitmap_has native_rank source_of_native get_tree].
  all: try (rewrite native_bucket_get_refines, pseq_length_view,
    bucket_get_index_spec; reflexivity).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
    change (native_bitmap_has bitmap (native_chunk full_hash depth) = true) in Hpresent.
    destruct (pseq_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild.
    + change (pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = Some child) in Hchild.
      rewrite Hpresent, Hchild.
      cbn [source_of_native get_tree].
      rewrite (@pseq_get_source_children K A
        (rank bitmap (chunk full_hash depth)) children child Hchild).
      now apply IH.
    + change (pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = None) in Hchild.
      rewrite Hpresent, Hchild.
      cbn [source_of_native get_tree].
      rewrite (@pseq_get_source_children_none K A
        (rank bitmap (chunk full_hash depth)) children Hchild).
      reflexivity.
    + change (native_bitmap_has bitmap (native_chunk full_hash depth) = false) in Hpresent.
      rewrite Hpresent. reflexivity.
Qed.

(** Public lookup is unrolled over the six routing depths.  Each level is a
    source-defined worker, and the equations below preserve the total fueled
    model even for arbitrary modeled trees.  Extraction therefore avoids the
    closure-producing [nat] case at every branch. *)
Definition native_get_depth6 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch _ _ => None
  end.

Lemma native_get_depth6_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth6 eqb full_hash key native =
    native_get eqb 0 6 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Definition native_get_depth5 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      let slot := native_chunk full_hash 5 in
      if native_bitmap_has bitmap slot then
        match pseq_get (native_rank bitmap slot) children with
        | Some child => native_get_depth6 eqb full_hash key child
        | None => None
        end
      else None
  end.

Lemma native_get_depth5_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth5 eqb full_hash key native =
    native_get eqb 1 5 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Definition native_get_depth4 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      let slot := native_chunk full_hash 4 in
      if native_bitmap_has bitmap slot then
        match pseq_get (native_rank bitmap slot) children with
        | Some child => native_get_depth5 eqb full_hash key child
        | None => None
        end
      else None
  end.

Lemma native_get_depth4_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth4 eqb full_hash key native =
    native_get eqb 2 4 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Definition native_get_depth3 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      let slot := native_chunk full_hash 3 in
      if native_bitmap_has bitmap slot then
        match pseq_get (native_rank bitmap slot) children with
        | Some child => native_get_depth4 eqb full_hash key child
        | None => None
        end
      else None
  end.

Lemma native_get_depth3_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth3 eqb full_hash key native =
    native_get eqb 3 3 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Definition native_get_depth2 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      let slot := native_chunk full_hash 2 in
      if native_bitmap_has bitmap slot then
        match pseq_get (native_rank bitmap slot) children with
        | Some child => native_get_depth3 eqb full_hash key child
        | None => None
        end
      else None
  end.

Lemma native_get_depth2_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth2 eqb full_hash key native =
    native_get eqb 4 2 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Definition native_get_depth1 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      let slot := native_chunk full_hash 1 in
      if native_bitmap_has bitmap slot then
        match pseq_get (native_rank bitmap slot) children with
        | Some child => native_get_depth2 eqb full_hash key child
        | None => None
        end
      else None
  end.

Lemma native_get_depth1_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth1 eqb full_hash key native =
    native_get eqb 5 1 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Definition native_get_depth0 {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (native : native_tree K A) : option A :=
  match native with
  | NativeEmpty => None
  | NativeLeaf stored_hash stored value =>
      if native_bounded_eq full_hash stored_hash then
        if eqb key stored then Some value else None
      else None
  | NativeCollision stored_hash entries =>
      if native_bounded_eq full_hash stored_hash then
        native_bucket_get eqb key entries 0 (pseq_length entries)
      else None
  | NativeBranch bitmap children =>
      let slot := native_chunk full_hash 0 in
      if native_bitmap_has bitmap slot then
        match pseq_get (native_rank bitmap slot) children with
        | Some child => native_get_depth1 eqb full_hash key child
        | None => None
        end
      else None
  end.

Lemma native_get_depth0_eq :
  forall K A (eqb : K -> K -> bool) full_hash (key : K)
         (native : native_tree K A),
    native_get_depth0 eqb full_hash key native =
    native_get eqb 6 0 full_hash key native.
Proof. intros. destruct native; reflexivity. Qed.

Lemma native_set_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         (native : native_tree K A),
    source_of_native (native_set eqb fuel depth full_hash key value native) =
    set_tree eqb fuel depth full_hash key value (source_of_native native).
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key value native;
    destruct native as [|stored_hash stored old|stored_hash entries|bitmap children].
  all: cbn [native_set native_chunk native_bitmap_has native_rank]; try apply source_of_native_of_source.
  all: try reflexivity.
  all: try apply native_leaf_set_refines.
  all: try apply native_collision_set_refines.
  destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
  - destruct (pseq_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild.
    + assert (Hnativepresent :
        native_bitmap_has bitmap (native_chunk full_hash depth) = true) by exact Hpresent.
      assert (Hnativechild :
        pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = Some child) by exact Hchild.
      rewrite Hnativepresent, Hnativechild.
      rewrite source_of_native_branch_replace_at.
      rewrite IH.
      cbn [source_of_native set_tree].
      rewrite Hpresent.
      rewrite (@pseq_get_source_children K A
        (rank bitmap (chunk full_hash depth)) children child Hchild).
      reflexivity.
    + assert (Hnativepresent :
        native_bitmap_has bitmap (native_chunk full_hash depth) = true) by exact Hpresent.
      assert (Hnativechild :
        pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = None) by exact Hchild.
      rewrite Hnativepresent, Hnativechild.
      rewrite source_of_native_branch_insert_at.
      cbn [source_of_native set_tree].
      rewrite Hpresent.
      rewrite (@pseq_get_source_children_none K A
        (rank bitmap (chunk full_hash depth)) children Hchild).
      reflexivity.
  - assert (Hnativepresent :
      native_bitmap_has bitmap (native_chunk full_hash depth) = false) by exact Hpresent.
    rewrite Hnativepresent.
    rewrite source_of_native_branch_insert_at.
    cbn [source_of_native set_tree].
    rewrite Hpresent.
    reflexivity.
Qed.

Lemma native_remove_refines :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A),
    source_of_native (native_remove eqb fuel depth full_hash key native) =
    remove_tree eqb fuel depth full_hash key (source_of_native native).
Proof.
  intros K A eqb fuel.
  induction fuel as [|fuel IH]; intros depth full_hash key native;
    destruct native as [|stored_hash stored value|stored_hash entries|bitmap children].
  all: cbn [native_remove]; try apply source_of_native_of_source.
  all: try reflexivity.
  all: try apply native_leaf_remove_refines.
  all: try apply native_collision_remove_refines.
  destruct (bitmap_has bitmap (chunk full_hash depth)) eqn:Hpresent.
  - destruct (pseq_get (rank bitmap (chunk full_hash depth)) children)
      as [child|] eqn:Hchild.
    + assert (Hnativepresent :
        native_bitmap_has bitmap (native_chunk full_hash depth) = true) by exact Hpresent.
      assert (Hnativechild :
        pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = Some child) by exact Hchild.
      rewrite Hnativepresent, Hnativechild.
      destruct (native_remove eqb fuel (S depth) full_hash key child)
        as [|child_hash child_key child_value|child_hash child_entries|child_bitmap child_children]
        eqn:Hremove.
      * rewrite source_of_native_branch_remove_at.
        cbn [source_of_native remove_tree].
        rewrite Hpresent.
        rewrite (@pseq_get_source_children K A
          (rank bitmap (chunk full_hash depth)) children child Hchild).
        rewrite <- (IH (S depth) full_hash key child).
        rewrite Hremove.
        reflexivity.
      * rewrite source_of_native_branch_replace_at.
        cbn [source_of_native remove_tree].
        rewrite Hpresent.
        rewrite (@pseq_get_source_children K A
          (rank bitmap (chunk full_hash depth)) children child Hchild).
        rewrite <- (IH (S depth) full_hash key child).
        rewrite Hremove.
        reflexivity.
      * rewrite source_of_native_branch_replace_at.
        cbn [source_of_native remove_tree].
        rewrite Hpresent.
        rewrite (@pseq_get_source_children K A
          (rank bitmap (chunk full_hash depth)) children child Hchild).
        rewrite <- (IH (S depth) full_hash key child).
        rewrite Hremove.
        reflexivity.
      * rewrite source_of_native_branch_replace_at.
        cbn [source_of_native remove_tree].
        rewrite Hpresent.
        rewrite (@pseq_get_source_children K A
          (rank bitmap (chunk full_hash depth)) children child Hchild).
        rewrite <- (IH (S depth) full_hash key child).
        rewrite Hremove.
        reflexivity.
    + assert (Hnativepresent :
        native_bitmap_has bitmap (native_chunk full_hash depth) = true) by exact Hpresent.
      assert (Hnativechild :
        pseq_get (native_rank bitmap (native_chunk full_hash depth)) children = None) by exact Hchild.
      rewrite Hnativepresent, Hnativechild.
      cbn [source_of_native remove_tree].
      rewrite Hpresent.
      rewrite (@pseq_get_source_children_none K A
        (rank bitmap (chunk full_hash depth)) children Hchild).
      reflexivity.
  - assert (Hnativepresent :
      native_bitmap_has bitmap (native_chunk full_hash depth) = false) by exact Hpresent.
    rewrite Hnativepresent.
    cbn [source_of_native remove_tree].
    rewrite Hpresent.
    reflexivity.
Qed.

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
  native_get_depth0 eqb (hash (native_table_seed native) key) key
    (native_table_root native).

Fixpoint native_table_add_first {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (entries : list (K * A))
    (native : native_table K Seed A) : native_table K Seed A :=
  match entries with
  | [] => native
  | (key, value) :: tail =>
      let next := match native_table_get eqb hash key native with
                  | Some _ => native
                  | None => native_table_set eqb hash key value native
                  end in
      native_table_add_first eqb hash tail next
  end.

Definition native_table_of_list {K Seed A : Type} (eqb : K -> K -> bool)
    (hash : Seed -> K -> N) (seed : Seed) (entries : list (K * A))
    : native_table K Seed A :=
  native_table_add_first eqb hash entries (native_empty seed).

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
  unfold native_table_get.
  rewrite native_get_depth0_eq.
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

Lemma source_table_native_add_first :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         entries (native : native_table K Seed A),
    source_table_of_native (native_table_add_first eqb hash entries native) =
    add_first eqb hash entries (source_table_of_native native).
Proof.
  intros K Seed A eqb hash entries.
  induction entries as [|[key value] tail IH]; intro native.
  - reflexivity.
  - simpl.
    destruct (native_table_get eqb hash key native) as [previous|] eqn:Hget.
    + rewrite native_table_get_refines in Hget.
      rewrite Hget. apply IH.
    + rewrite native_table_get_refines in Hget.
      rewrite Hget.
      pose proof (IH (native_table_set eqb hash key value native)) as Htail.
      rewrite source_table_native_set in Htail. exact Htail.
Qed.

Lemma source_table_native_of_list :
  forall K Seed A (eqb : K -> K -> bool) (hash : Seed -> K -> N)
         (seed : Seed) (entries : list (K * A)),
    source_table_of_native (native_table_of_list eqb hash seed entries) =
    of_list eqb hash seed entries.
Proof.
  intros K Seed A eqb hash seed entries.
  unfold native_table_of_list, of_list.
  rewrite source_table_native_add_first.
  rewrite source_table_native_empty. reflexivity.
Qed.

Lemma native_table_elements_refines :
  forall K Seed A (native : native_table K Seed A),
    native_table_elements native = elements (source_table_of_native native).
Proof. reflexivity. Qed.

Lemma native_table_is_empty_refines :
  forall K Seed A (native : native_table K Seed A),
    native_table_is_empty native = is_empty (source_table_of_native native).
Proof. intros K Seed A [seed root]; destruct root; reflexivity. Qed.
