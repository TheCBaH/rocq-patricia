From Stdlib Require Import Bool List PeanoNat Strings.String.
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

Definition mem {A : Type} (key : string) (m : t A) : bool :=
  match get key m with Some _ => true | None => false end.

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

Definition set {A : Type} (key : string) (value : A) (m : t A) : t A :=
  match routed_key key m with
  | None => Leaf key value
  | Some routed =>
      match first_diff key routed with
      | None => replace key value m
      | Some differing => insert_at key value differing m
      end
  end.

Fixpoint remove {A : Type} (key : string) (m : t A) : t A :=
  match m with
  | Empty => Empty
  | Leaf stored _ => if String.eqb key stored then Empty else m
  | Branch sample split ltree rtree =>
      if bit_at key split
      then branch sample split ltree (remove key rtree)
      else branch sample split (remove key ltree) rtree
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
      | Leaf ka va, _ =>
          replace_binding ka (f (Some va) (get ka b)) (map_right f b)
      | _, Leaf kb vb =>
          replace_binding kb (f (get kb a) (Some vb)) (map_left f a)
      | Branch sample_a split_a left_a right_a,
        Branch sample_b split_b left_b right_b =>
          if split_a =? split_b then
            if agrees_before sample_a sample_b split_a then
              branch sample_a split_a
                (combine_fuel fuel' f left_a left_b)
                (combine_fuel fuel' f right_a right_b)
            else join (map_left f a) (map_right f b)
          else if split_a <? split_b then
            if agrees_before sample_a sample_b split_a then
              if bit_at sample_b split_a
              then branch sample_a split_a (map_left f left_a)
                     (combine_fuel fuel' f right_a b)
              else branch sample_a split_a
                     (combine_fuel fuel' f left_a b) (map_left f right_a)
            else join (map_left f a) (map_right f b)
          else
            if agrees_before sample_a sample_b split_b then
              if bit_at sample_a split_b
              then branch sample_b split_b (map_right f left_b)
                     (combine_fuel fuel' f a right_b)
              else branch sample_b split_b
                     (combine_fuel fuel' f a left_b) (map_right f right_b)
            else join (map_left f a) (map_right f b)
      end
  end.

Definition combine {A B C : Type}
    (f : option A -> option B -> option C) (a : t A) (b : t B) : t C :=
  combine_fuel (S (size a + size b)) f a b.

Definition union_left {A : Type} (a b : t A) : t A :=
  combine (fun x y => match x with Some _ => x | None => y end) a b.

Definition union_right {A : Type} (a b : t A) : t A :=
  combine (fun x y => match y with Some _ => y | None => x end) a b.

Fixpoint elements {A : Type} (m : t A) : list (string * A) :=
  match m with
  | Empty => []
  | Leaf key value => [(key, value)]
  | Branch _ _ ltree rtree => elements ltree ++ elements rtree
  end.

Fixpoint fold {A B : Type}
    (f : B -> string -> A -> B) (m : t A) (acc : B) : B :=
  match m with
  | Empty => acc
  | Leaf key value => f acc key value
  | Branch _ _ ltree rtree => fold f rtree (fold f ltree acc)
  end.
