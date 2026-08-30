(** An executable, standalone sketch of Okasaki--Gill mergeable integer maps.

    The constructors are deliberately visible in this prototype.  Production
    clients should hide them behind a module signature and only expose values
    produced by the smart constructors below. *)

From Stdlib Require Import Arith.Wf_nat Bool Lia List NArith PArith Program.Wf.
Import ListNotations.

Require Import PatriciaBits.

Set Implicit Arguments.

Inductive t (A : Type) : Type :=
| Empty
| Leaf (key : positive) (value : A)
| Branch (prefix mask : N) (left right : t A).

Arguments Empty {A}.
Arguments Leaf {A} _ _.
Arguments Branch {A} _ _ _ _.

Definition empty {A : Type} : t A := Empty.

Definition is_empty {A : Type} (m : t A) : bool :=
  match m with Empty => true | _ => false end.

Definition singleton {A : Type} (k : positive) (v : A) : t A := Leaf k v.

Fixpoint get {A : Type} (k : positive) (m : t A) : option A :=
  match m with
  | Empty => None
  | Leaf j v => if Pos.eqb k j then Some v else None
  | Branch p mask l r =>
      if matches_prefix k p mask then
        if zero_bit k mask then get k l else get k r
      else None
  end.

Fixpoint mem {A : Type} (k : positive) (m : t A) : bool :=
  match m with
  | Empty => false
  | Leaf j _ => Pos.eqb k j
  | Branch p mask l r =>
      if matches_prefix k p mask then
        if zero_bit k mask then mem k l else mem k r
      else false
  end.

Fixpoint representative {A : Type} (m : t A) : option positive :=
  match m with
  | Empty => None
  | Leaf k _ => Some k
  | Branch _ _ l r =>
      match representative l with
      | Some k => Some k
      | None => representative r
      end
  end.

(** [branch] is the sole constructor used after deletion/filtering; it removes
    empty internal nodes and therefore keeps successful results compressed. *)
Definition branch {A : Type} (p mask : N) (l r : t A) : t A :=
  match l, r with
  | Empty, _ => r
  | _, Empty => l
  | _, _ => Branch p mask l r
  end.

(** Join two non-overlapping tries at their highest differing bit.  The first
    argument wins in the defensive equal-representative case. *)
Definition join {A : Type} (a b : t A) : t A :=
  match representative a, representative b with
  | None, _ => b
  | _, None => a
  | Some ka, Some kb =>
      if Pos.eqb ka kb then a
      else
        let mask := highest_differing_bit ka kb in
        let p := prefix ka mask in
        if zero_bit ka mask
        then Branch p mask a b
        else Branch p mask b a
  end.

Fixpoint set {A : Type} (k : positive) (v : A) (m : t A) : t A :=
  match m with
  | Empty => Leaf k v
  | Leaf j _ as old =>
      if Pos.eqb k j then Leaf k v else join (Leaf k v) old
  | Branch p mask l r as old =>
      if matches_prefix k p mask then
        if zero_bit k mask
        then Branch p mask (set k v l) r
        else Branch p mask l (set k v r)
      else join (Leaf k v) old
  end.

(* This structural version is kept as a simple proof reference.  The public
   deletion below uses [None] to propagate an unchanged result without
   rebuilding the routed path. *)
Fixpoint remove_reference {A : Type} (k : positive) (m : t A) : t A :=
  match m with
  | Empty => Empty
  | Leaf j _ => if Pos.eqb k j then Empty else m
  | Branch p mask l r =>
      if matches_prefix k p mask then
        if zero_bit k mask
        then branch p mask (remove_reference k l) r
        else branch p mask l (remove_reference k r)
      else m
  end.

Fixpoint remove_changed {A : Type} (k : positive) (m : t A)
    : option (t A) :=
  match m with
  | Empty => None
  | Leaf j _ => if Pos.eqb k j then Some Empty else None
  | Branch p mask l r =>
      if matches_prefix k p mask then
        if zero_bit k mask then
          match remove_changed k l with
          | None => None
          | Some l' => Some (branch p mask l' r)
          end
        else
          match remove_changed k r with
          | None => None
          | Some r' => Some (branch p mask l r')
          end
      else None
  end.

Definition remove {A : Type} (k : positive) (m : t A) : t A :=
  match remove_changed k m with
  | None => m
  | Some changed => changed
  end.

Fixpoint map {A B : Type} (f : positive -> A -> B) (m : t A) : t B :=
  match m with
  | Empty => Empty
  | Leaf k v => Leaf k (f k v)
  | Branch p mask l r => Branch p mask (map f l) (map f r)
  end.

Fixpoint map_filter {A B : Type}
    (f : positive -> A -> option B) (m : t A) : t B :=
  match m with
  | Empty => Empty
  | Leaf k v =>
      match f k v with Some w => Leaf k w | None => Empty end
  | Branch p mask l r =>
      branch p mask (map_filter f l) (map_filter f r)
  end.

Definition map_left {A B C : Type}
    (f : option A -> option B -> option C) (m : t A) : t C :=
  map_filter (fun _ v => f (Some v) None) m.

Definition map_right {A B C : Type}
    (f : option A -> option B -> option C) (m : t B) : t C :=
  map_filter (fun _ v => f None (Some v)) m.

Definition replace_binding {A : Type}
    (k : positive) (v : option A) (m : t A) : t A :=
  match v with Some x => set k x m | None => remove k m end.

(** Fuse the replacement of an overlapping leaf into the whole-tree
    transformation.  An absent leaf still uses the ordinary mapped-tree
    insertion path; the preceding lookup determines which case applies. *)
Definition combine_leaf_left {A B C : Type}
    (f : option A -> option B -> option C)
    (key : positive) (value : A) (m : t B) : t C :=
  match get key m with
  | Some _ =>
      map_filter (fun stored right =>
        if Pos.eqb stored key
        then f (Some value) (Some right)
        else f None (Some right)) m
  | None =>
      replace_binding key (f (Some value) None) (map_right f m)
  end.

Definition combine_leaf_right {A B C : Type}
    (f : option A -> option B -> option C)
    (m : t A) (key : positive) (value : B) : t C :=
  match get key m with
  | Some _ =>
      map_filter (fun stored left =>
        if Pos.eqb stored key
        then f (Some left) (Some value)
        else f (Some left) None) m
  | None =>
      replace_binding key (f None (Some value)) (map_left f m)
  end.

Fixpoint size {A : Type} (m : t A) : nat :=
  match m with
  | Empty => 0
  | Leaf _ _ => 1
  | Branch _ _ l r => S (size l + size r)
  end.

(** Fuel makes the prototype's general merge definition transparently total.
    Recursive calls consume one unit; the public bound exceeds the combined
    structural depth.  Branch/branch cases are the fast Patricia cases: equal
    prefixes recurse pairwise, containment recurses into only the overlapping
    child, and disjoint prefixes reuse both mapped subtries wholesale. *)
Fixpoint combine_fuel {A B C : Type}
    (fuel : nat) (f : option A -> option B -> option C)
    (a : t A) (b : t B) : t C :=
  match fuel with
  | O => Empty
  | S fuel' =>
      match a, b with
      | Empty, _ => map_right f b
      | _, Empty => map_left f a
      | Leaf ka va, _ =>
          replace_binding ka (f (Some va) (get ka b)) (map_right f b)
      | _, Leaf kb vb =>
          replace_binding kb (f (get kb a) (Some vb)) (map_left f a)
      | Branch pa ma la ra, Branch pb mb lb rb =>
          if (N.eqb ma mb && N.eqb pa pb)%bool then
            branch pa ma
              (combine_fuel fuel' f la lb)
              (combine_fuel fuel' f ra rb)
          else if mask_above ma mb then
            match representative b with
            | None => map_left f a
            | Some kb =>
                if matches_prefix kb pa ma then
                  if zero_bit kb ma then
                    branch pa ma
                      (combine_fuel fuel' f la b) (map_left f ra)
                  else
                    branch pa ma
                      (map_left f la) (combine_fuel fuel' f ra b)
                else join (map_left f a) (map_right f b)
            end
          else if mask_above mb ma then
            match representative a with
            | None => map_right f b
            | Some ka =>
                if matches_prefix ka pb mb then
                  if zero_bit ka mb then
                    branch pb mb
                      (combine_fuel fuel' f a lb) (map_right f rb)
                  else
                    branch pb mb
                      (map_right f lb) (combine_fuel fuel' f a rb)
                else join (map_left f a) (map_right f b)
            end
          else join (map_left f a) (map_right f b)
      end
  end.

(** The fuelled worker above is the simple termination reference.  The public
    worker uses the same Patricia cases, but recurses directly on the strictly
    smaller combined size of its arguments. *)
Program Fixpoint combine_structural {A B C : Type}
    (f : option A -> option B -> option C)
    (a : t A) (b : t B) {measure (size a + size b)%nat} : t C :=
  match a, b with
  | Empty, _ => map_right f b
  | _, Empty => map_left f a
  | Leaf ka va, _ =>
      replace_binding ka (f (Some va) (get ka b)) (map_right f b)
  | _, Leaf kb vb =>
      replace_binding kb (f (get kb a) (Some vb)) (map_left f a)
  | Branch pa ma la ra, Branch pb mb lb rb =>
      if (N.eqb ma mb && N.eqb pa pb)%bool then
        branch pa ma
          (combine_structural f la lb)
          (combine_structural f ra rb)
      else if mask_above ma mb then
        match representative b with
        | None => map_left f a
        | Some kb =>
            if matches_prefix kb pa ma then
              if zero_bit kb ma then
                branch pa ma
                  (combine_structural f la b) (map_left f ra)
              else
                branch pa ma
                  (map_left f la) (combine_structural f ra b)
            else join (map_left f a) (map_right f b)
        end
      else if mask_above mb ma then
        match representative a with
        | None => map_right f b
        | Some ka =>
            if matches_prefix ka pb mb then
              if zero_bit ka mb then
                branch pb mb
                  (combine_structural f a lb) (map_right f rb)
              else
                branch pb mb
                  (map_right f lb) (combine_structural f a rb)
            else join (map_left f a) (map_right f b)
        end
      else join (map_left f a) (map_right f b)
  end.
Next Obligation. intros; cbn [size]; lia. Qed.
Next Obligation. intros; cbn [size]; lia. Qed.
Next Obligation. intros; cbn in *; lia. Qed.
Next Obligation. intros; cbn in *; lia. Qed.
Next Obligation. intros; cbn in *; lia. Qed.
Next Obligation. intros; cbn in *; lia. Qed.
Next Obligation. split; intros; intuition discriminate. Qed.

Definition combine {A B C : Type}
    (f : option A -> option B -> option C) (a : t A) (b : t B) : t C :=
  combine_structural f a b.

Definition union_left {A : Type} (a b : t A) : t A :=
  combine (fun x y => match x with Some _ => x | None => y end) a b.

Definition union_right {A : Type} (a b : t A) : t A :=
  combine (fun x y => match y with Some _ => y | None => x end) a b.

Fixpoint elements_aux {A : Type}
    (m : t A) (tail : list (positive * A)) : list (positive * A) :=
  match m with
  | Empty => tail
  | Leaf k v => (k, v) :: tail
  | Branch _ _ l r => elements_aux l (elements_aux r tail)
  end.

Definition elements {A : Type} (m : t A) : list (positive * A) :=
  elements_aux m [].

Fixpoint fold {A B : Type}
    (f : B -> positive -> A -> B) (m : t A) (acc : B) : B :=
  match m with
  | Empty => acc
  | Leaf k v => f acc k v
  | Branch _ _ l r => fold f r (fold f l acc)
  end.

Fixpoint forallb {A : Type}
    (f : positive -> A -> bool) (m : t A) : bool :=
  match m with
  | Empty => true
  | Leaf k v => f k v
  | Branch _ _ l r => forallb f l && forallb f r
  end.

Definition beq {A : Type} (eqA : A -> A -> bool) (a b : t A) : bool :=
  forallb
    (fun k v => match get k b with Some w => eqA v w | None => false end) a
  && forallb
    (fun k v => match get k a with Some w => eqA w v | None => false end) b.
