From Stdlib Require Import Arith.Wf_nat Bool Lia List PeanoNat Program.Wf
  Strings.String.
Import ListNotations.

Require Import StringBits.

Set Implicit Arguments.

Inductive t (A : Type) : Type :=
| Empty
| Leaf (key : string) (value : A)
| Branch (sample : string) (split : nat) (left right : t A).

Arguments Empty {A}.
Arguments Leaf {A} _ _.
Arguments Branch {A} _ _ _ _.

Definition empty {A : Type} : t A := Empty.

Definition is_empty {A : Type} (m : t A) : bool :=
  match m with Empty => true | _ => false end.

Definition singleton {A : Type} (key : string) (value : A) : t A :=
  Leaf key value.

Fixpoint representative {A : Type} (m : t A) : option string :=
  match m with
  | Empty => None
  | Leaf key _ => Some key
  | Branch _ _ ltree rtree =>
      match representative ltree with
      | Some key => Some key
      | None => representative rtree
      end
  end.

Fixpoint get {A : Type} (key : string) (m : t A) : option A :=
  match m with
  | Empty => None
  | Leaf stored value => if String.eqb key stored then Some value else None
  | Branch _ split ltree rtree =>
      if bit_at key split then get key rtree else get key ltree
  end.

Fixpoint mem {A : Type} (key : string) (m : t A) : bool :=
  match m with
  | Empty => false
  | Leaf stored _ => String.eqb key stored
  | Branch _ split ltree rtree =>
      if bit_at key split then mem key rtree else mem key ltree
  end.

Definition branch {A : Type}
    (sample : string) (split : nat) (ltree rtree : t A) : t A :=
  match ltree, rtree with
  | Empty, _ => rtree
  | _, Empty => ltree
  | _, _ =>
      match representative ltree with
      | Some key => Branch key split ltree rtree
      | None => Branch sample split ltree rtree
      end
  end.

Definition branch_at {A : Type}
    (sample : string) (split : nat) (fresh old : t A) : t A :=
  if bit_at sample split
  then Branch sample split old fresh
  else Branch sample split fresh old.

Definition join {A : Type} (fresh old : t A) : t A :=
  match representative fresh, representative old with
  | None, _ => old
  | _, None => fresh
  | Some fresh_key, Some old_key =>
      match first_diff fresh_key old_key with
      | None => fresh
      | Some split => branch_at fresh_key split fresh old
      end
  end.

Fixpoint replace {A : Type}
    (key : string) (value : A) (m : t A) : t A :=
  match m with
  | Empty => Leaf key value
  | Leaf _ _ => Leaf key value
  | Branch sample split ltree rtree =>
      if bit_at key split
      then Branch sample split ltree (replace key value rtree)
      else Branch sample split (replace key value ltree) rtree
  end.

Fixpoint insert_at {A : Type}
    (key : string) (value : A) (differing : nat) (m : t A) : t A :=
  match m with
  | Empty => Leaf key value
  | Leaf _ _ => branch_at key differing (Leaf key value) m
  | Branch sample split ltree rtree =>
      if differing <? split then branch_at key differing (Leaf key value) m
      else if bit_at key split
           then Branch sample split ltree (insert_at key value differing rtree)
           else Branch sample split (insert_at key value differing ltree) rtree
  end.

Fixpoint routed_key {A : Type} (key : string) (m : t A) : option string :=
  match m with
  | Empty => None
  | Leaf stored _ => Some stored
  | Branch _ split ltree rtree =>
      if bit_at key split then routed_key key rtree else routed_key key ltree
  end.

(** The result carried by the proof-side counterpart of the native
    exception-based update.  A [Set_bubble] result records the first split
    discovered at a leaf and propagates it only until the first enclosing
    branch below which the fresh binding belongs. *)
Inductive set_descent_result (A : Type) : Type :=
| Set_complete (updated : t A)
| Set_bubble (differing : nat).

Arguments Set_complete {A} _.
Arguments Set_bubble {A} _.

(** This follows the native [set] realizer's control flow without using an
    exception.  It descends only once: an existing key is replaced at its
    leaf, while a fresh key's first-difference position bubbles upward until
    it can be installed.  [set] below remains the established specification;
    [StringPatriciaProof.v] will establish the refinement theorem before this
    worker is extracted. *)
Fixpoint set_descend {A : Type}
    (key : string) (value : A) (m : t A) : set_descent_result A :=
  let fresh := Leaf key value in
  match m with
  | Empty => Set_complete fresh
  | Leaf stored _ =>
      match first_diff key stored with
      | None => Set_complete fresh
      | Some differing => Set_bubble differing
      end
  | Branch sample split ltree rtree =>
      if bit_at key split then
        match set_descend key value rtree with
        | Set_complete updated => Set_complete (Branch sample split ltree updated)
        | Set_bubble differing =>
            if differing <? split then Set_bubble differing
            else Set_complete
                   (Branch sample split ltree
                      (branch_at key differing fresh rtree))
        end
      else
        match set_descend key value ltree with
        | Set_complete updated => Set_complete (Branch sample split updated rtree)
        | Set_bubble differing =>
            if differing <? split then Set_bubble differing
            else Set_complete
                   (Branch sample split
                      (branch_at key differing fresh ltree) rtree)
        end
  end.

Definition set_one_descent {A : Type}
    (key : string) (value : A) (m : t A) : t A :=
  match set_descend key value m with
  | Set_complete updated => updated
  | Set_bubble differing => branch_at key differing (Leaf key value) m
  end.

(** This allocation-aware variant has the same control flow as
    [set_descend], but receives the new leaf as an argument.  Ordinary OCaml
    extraction consequently allocates that leaf once for the entire descent,
    rather than once at every recursive call. *)
Fixpoint set_descend_shared {A : Type}
    (key : string) (fresh : t A) (m : t A) : set_descent_result A :=
  match m with
  | Empty => Set_complete fresh
  | Leaf stored _ =>
      match first_diff key stored with
      | None => Set_complete fresh
      | Some differing => Set_bubble differing
      end
  | Branch sample split ltree rtree =>
      if bit_at key split then
        match set_descend_shared key fresh rtree with
        | Set_complete updated => Set_complete (Branch sample split ltree updated)
        | Set_bubble differing =>
            if differing <? split then Set_bubble differing
            else Set_complete
                   (Branch sample split ltree
                      (branch_at key differing fresh rtree))
        end
      else
        match set_descend_shared key fresh ltree with
        | Set_complete updated => Set_complete (Branch sample split updated rtree)
        | Set_bubble differing =>
            if differing <? split then Set_bubble differing
            else Set_complete
                   (Branch sample split
                      (branch_at key differing fresh ltree) rtree)
        end
  end.

Definition set_one_descent_shared {A : Type}
    (key : string) (value : A) (m : t A) : t A :=
  let fresh := Leaf key value in
  match set_descend_shared key fresh m with
  | Set_complete updated => updated
  | Set_bubble differing => branch_at key differing fresh m
  end.

Definition set {A : Type} (key : string) (value : A) (m : t A) : t A :=
  match routed_key key m with
  | None => Leaf key value
  | Some routed =>
      match first_diff key routed with
      | None => replace key value m
      | Some differing => insert_at key value differing m
      end
  end.

(** A separately named copy of the public source update. It provides a
    directly measurable ordinary-extraction baseline for the two-descent
    algorithm. *)
Definition set_two_descent {A : Type} (key : string) (value : A) (m : t A) : t A :=
  match routed_key key m with
  | None => Leaf key value
  | Some routed =>
      match first_diff key routed with
      | None => replace key value m
      | Some differing => insert_at key value differing m
      end
  end.

(** Build a map from a batch of bindings.  Earlier bindings take precedence
    over later bindings with the same key, matching the recursive order below.
    This remains inside the proved source model instead of exposing a raw
    constructor-based loader through the OCaml interface. *)
Fixpoint of_list {A : Type} (bindings : list (string * A)) : t A :=
  match bindings with
  | [] => Empty
  | (key, value) :: tail => set key value (of_list tail)
  end.

(** Lookup model for [of_list]; the first binding for a duplicate key wins. *)
Fixpoint of_list_get {A : Type}
    (query : string) (bindings : list (string * A)) : option A :=
  match bindings with
  | [] => None
  | (key, value) :: tail =>
      if String.eqb query key then Some value else of_list_get query tail
  end.

(* This structural version is kept as a simple proof reference.  The public
   deletion below uses [None] to propagate an unchanged result without
   rebuilding the routed path. *)
Fixpoint remove_reference {A : Type} (key : string) (m : t A) : t A :=
  match m with
  | Empty => Empty
  | Leaf stored _ => if String.eqb key stored then Empty else m
  | Branch sample split ltree rtree =>
      if bit_at key split
      then branch sample split ltree (remove_reference key rtree)
      else branch sample split (remove_reference key ltree) rtree
  end.

Fixpoint remove_changed {A : Type} (key : string) (m : t A)
    : option (t A) :=
  match m with
  | Empty => None
  | Leaf stored _ => if String.eqb key stored then Some Empty else None
  | Branch sample split ltree rtree =>
      if bit_at key split then
        match remove_changed key rtree with
        | None => None
        | Some rtree' => Some (branch sample split ltree rtree')
        end
      else
        match remove_changed key ltree with
        | None => None
        | Some ltree' => Some (branch sample split ltree' rtree)
        end
  end.

Definition remove {A : Type} (key : string) (m : t A) : t A :=
  match remove_changed key m with
  | None => m
  | Some changed => changed
  end.

Fixpoint map {A B : Type} (f : string -> A -> B) (m : t A) : t B :=
  match m with
  | Empty => Empty
  | Leaf key value => Leaf key (f key value)
  | Branch sample split ltree rtree =>
      Branch sample split (map f ltree) (map f rtree)
  end.

Fixpoint map_filter {A B : Type}
    (f : string -> A -> option B) (m : t A) : t B :=
  match m with
  | Empty => Empty
  | Leaf key value =>
      match f key value with Some result => Leaf key result | None => Empty end
  | Branch sample split ltree rtree =>
      branch sample split (map_filter f ltree) (map_filter f rtree)
  end.

Definition map_left {A B C : Type}
    (f : option A -> option B -> option C) (m : t A) : t C :=
  map_filter (fun _ value => f (Some value) None) m.

Definition map_right {A B C : Type}
    (f : option A -> option B -> option C) (m : t B) : t C :=
  map_filter (fun _ value => f None (Some value)) m.

Definition replace_binding {A : Type}
    (key : string) (value : option A) (m : t A) : t A :=
  match value with Some result => set key result m | None => remove key m end.

(** Fuse the replacement of an overlapping leaf into the whole-tree
    transformation.  An absent leaf still uses the ordinary mapped-tree
    insertion path; the preceding lookup determines which case applies. *)
Definition combine_leaf_left {A B C : Type}
    (f : option A -> option B -> option C)
    (key : string) (value : A) (m : t B) : t C :=
  match get key m with
  | Some _ =>
      map_filter (fun stored right =>
        if String.eqb stored key
        then f (Some value) (Some right)
        else f None (Some right)) m
  | None =>
      replace_binding key (f (Some value) None) (map_right f m)
  end.

Definition combine_leaf_right {A B C : Type}
    (f : option A -> option B -> option C)
    (m : t A) (key : string) (value : B) : t C :=
  match get key m with
  | Some _ =>
      map_filter (fun stored left =>
        if String.eqb stored key
        then f (Some left) (Some value)
        else f (Some left) None) m
  | None =>
      replace_binding key (f None (Some value)) (map_left f m)
  end.

Fixpoint size {A : Type} (m : t A) : nat :=
  match m with
  | Empty => 0
  | Leaf _ _ => 1
  | Branch _ _ ltree rtree => S (size ltree + size rtree)
  end.

Fixpoint combine_fuel {A B C : Type}
    (fuel : nat) (f : option A -> option B -> option C)
    (a : t A) (b : t B) : t C :=
  match fuel with
  | 0 => Empty
  | S fuel' =>
      match a, b with
      | Empty, _ => map_right f b
      | _, Empty => map_left f a
      | Leaf ka va, _ => combine_leaf_left f ka va b
      | _, Leaf kb vb => combine_leaf_right f a kb vb
      | Branch sample_a split_a left_a right_a,
        Branch sample_b split_b left_b right_b =>
          if split_a =? split_b then
            if agrees_before_bounded sample_a sample_b split_a then
              branch sample_a split_a
                (combine_fuel fuel' f left_a left_b)
                (combine_fuel fuel' f right_a right_b)
            else join (map_left f a) (map_right f b)
          else if split_a <? split_b then
            if agrees_before_bounded sample_a sample_b split_a then
              if bit_at sample_b split_a
              then branch sample_a split_a (map_left f left_a)
                     (combine_fuel fuel' f right_a b)
              else branch sample_a split_a
                     (combine_fuel fuel' f left_a b) (map_left f right_a)
            else join (map_left f a) (map_right f b)
          else
            if agrees_before_bounded sample_a sample_b split_b then
              if bit_at sample_a split_b
              then branch sample_b split_b (map_right f left_b)
                     (combine_fuel fuel' f a right_b)
              else branch sample_b split_b
                     (combine_fuel fuel' f a left_b) (map_right f right_b)
            else join (map_left f a) (map_right f b)
      end
  end.

(** The fuelled worker above is the simple termination reference.  Nested
    structural recursion expresses the same decreasing calls directly: the
    outer fixpoint handles a smaller [a], and the local fixpoint handles a
    smaller [b] while [a] is unchanged.  This also keeps unfolding in the
    equivalence proof small and predictable. *)
Fixpoint combine_structural {A B C : Type}
    (f : option A -> option B -> option C) (a : t A) {struct a}
    : t B -> t C :=
  match a with
  | Empty => fun b => map_right f b
  | Leaf ka va => fun b => combine_leaf_left f ka va b
  | Branch sample_a split_a left_a right_a =>
      fix combine_right (b : t B) {struct b} : t C :=
        match b with
        | Empty => map_left f a
        | Leaf kb vb => combine_leaf_right f a kb vb
        | Branch sample_b split_b left_b right_b =>
            if split_a =? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                branch sample_a split_a
                  (combine_structural f left_a left_b)
                  (combine_structural f right_a right_b)
              else join (map_left f a) (map_right f b)
            else if split_a <? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                if bit_at sample_b split_a
                then branch sample_a split_a (map_left f left_a)
                       (combine_structural f right_a b)
                else branch sample_a split_a
                       (combine_structural f left_a b) (map_left f right_a)
              else join (map_left f a) (map_right f b)
            else
              if agrees_before_bounded sample_a sample_b split_b then
                if bit_at sample_a split_b
                then branch sample_b split_b (map_right f left_b)
                       (combine_right right_b)
                else branch sample_b split_b
                       (combine_right left_b) (map_right f right_b)
              else join (map_left f a) (map_right f b)
        end
  end.

(** Compact two-argument unfolding, folding the local right-tree recursion
    back to calls of the public structural worker. *)
Lemma combine_structural_equation:
  forall (A B C : Type) (f : option A -> option B -> option C)
      (a : t A) (b : t B),
    combine_structural f a b =
    match a, b with
    | Empty, _ => map_right f b
    | _, Empty => map_left f a
    | Leaf ka va, _ => combine_leaf_left f ka va b
    | _, Leaf kb vb => combine_leaf_right f a kb vb
    | Branch sample_a split_a left_a right_a,
      Branch sample_b split_b left_b right_b =>
        if split_a =? split_b then
          if agrees_before_bounded sample_a sample_b split_a then
            branch sample_a split_a
              (combine_structural f left_a left_b)
              (combine_structural f right_a right_b)
          else join (map_left f a) (map_right f b)
        else if split_a <? split_b then
          if agrees_before_bounded sample_a sample_b split_a then
            if bit_at sample_b split_a
            then branch sample_a split_a (map_left f left_a)
                   (combine_structural f right_a b)
            else branch sample_a split_a
                   (combine_structural f left_a b) (map_left f right_a)
          else join (map_left f a) (map_right f b)
        else
          if agrees_before_bounded sample_a sample_b split_b then
            if bit_at sample_a split_b
            then branch sample_b split_b (map_right f left_b)
                   (combine_structural f a right_b)
            else branch sample_b split_b
                   (combine_structural f a left_b) (map_right f right_b)
          else join (map_left f a) (map_right f b)
    end.
Proof. intros A B C f a b. destruct a; destruct b; reflexivity. Qed.

Definition combine {A B C : Type}
    (f : option A -> option B -> option C) (a : t A) (b : t B) : t C :=
  combine_structural f a b.

Definition union_left {A : Type} (a b : t A) : t A :=
  combine (fun x y => match x with Some _ => x | None => y end) a b.

Definition union_right {A : Type} (a b : t A) : t A :=
  combine (fun x y => match y with Some _ => y | None => x end) a b.

Fixpoint elements_aux {A : Type}
    (m : t A) (tail : list (string * A)) : list (string * A) :=
  match m with
  | Empty => tail
  | Leaf key value => (key, value) :: tail
  | Branch _ _ ltree rtree => elements_aux ltree (elements_aux rtree tail)
  end.

Definition elements {A : Type} (m : t A) : list (string * A) :=
  elements_aux m [].

Fixpoint fold {A B : Type}
    (f : B -> string -> A -> B) (m : t A) (acc : B) : B :=
  match m with
  | Empty => acc
  | Leaf key value => f acc key value
  | Branch _ _ ltree rtree => fold f rtree (fold f ltree acc)
  end.

Fixpoint forallb {A : Type}
    (f : string -> A -> bool) (m : t A) : bool :=
  match m with
  | Empty => true
  | Leaf key value => f key value
  | Branch _ _ ltree rtree => forallb f ltree && forallb f rtree
  end.

Definition beq {A : Type} (eqA : A -> A -> bool) (left right : t A) : bool :=
  forallb
    (fun key value =>
      match get key right with
      | Some other => eqA value other
      | None => false
      end) left
  && forallb
    (fun key value =>
      match get key left with
      | Some other => eqA other value
      | None => false
      end) right.
