(** Experimental source counterpart of the optimized direct-string biased
    union, isolated from the established string-map proof closure. *)

From Stdlib Require Import Bool PeanoNat Strings.String.
Require Import StringBits StringPatricia.

Fixpoint union_left_specialized {A : Type} (a : t A) {struct a}
    : t A -> t A :=
  match a with
  | Empty => fun b => b
  | Leaf ka va => fun b =>
      match b with
      | Empty => a
      | Leaf kb _ => if String.eqb ka kb then a else set ka va b
      | Branch _ _ _ _ => set ka va b
      end
  | Branch sample_a split_a left_a right_a =>
      fix union_right_tree (b : t A) {struct b} : t A :=
        match b with
        | Empty => a
        | Leaf kb vb =>
            match get kb a with Some _ => a | None => set kb vb a end
        | Branch sample_b split_b left_b right_b =>
            if split_a =? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                branch sample_a split_a
                  (union_left_specialized left_a left_b)
                  (union_left_specialized right_a right_b)
              else join a b
            else if split_a <? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                if bit_at sample_b split_a then
                  branch sample_a split_a left_a
                    (union_left_specialized right_a b)
                else branch sample_a split_a
                    (union_left_specialized left_a b) right_a
              else join a b
            else
              if agrees_before_bounded sample_a sample_b split_b then
                if bit_at sample_a split_b then
                  branch sample_b split_b left_b (union_right_tree right_b)
                else branch sample_b split_b (union_right_tree left_b) right_b
              else join a b
        end
  end.

(** Source-visible changed-result worker.  [Empty] means that the caller can
    reuse its original left tree directly after ordinary extraction, without
    an OCaml physical-equality test.  A changed biased union cannot be empty,
    so the nullary tree constructor is an allocation-free reuse sentinel. *)
Fixpoint union_left_specialized_changed {A : Type} (a : t A) {struct a}
    : t A -> t A :=
  match a with
  | Empty => fun b => b
  | Leaf ka va => fun b =>
      match b with
      | Empty => Empty
      | Leaf kb _ => if String.eqb ka kb then Empty else set ka va b
      | Branch _ _ _ _ => set ka va b
      end
  | Branch sample_a split_a left_a right_a =>
      fix union_right_tree (b : t A) {struct b} : t A :=
        match b with
        | Empty => Empty
        | Leaf kb vb =>
            match get kb a with Some _ => Empty | None => set kb vb a end
        | Branch sample_b split_b left_b right_b =>
            if split_a =? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                match union_left_specialized_changed left_a left_b,
                      union_left_specialized_changed right_a right_b with
                | Empty, Empty => Empty
                | left', Empty => branch sample_a split_a left' right_a
                | Empty, right' => branch sample_a split_a left_a right'
                | left', right' => branch sample_a split_a left' right'
                end
              else join a b
            else if split_a <? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                if bit_at sample_b split_a then
                  match union_left_specialized_changed right_a b with
                  | Empty => Empty
                  | right' => branch sample_a split_a left_a right'
                  end
                else
                  match union_left_specialized_changed left_a b with
                  | Empty => Empty
                  | left' => branch sample_a split_a left' right_a
                  end
              else join a b
            else
              if agrees_before_bounded sample_a sample_b split_b then
                if bit_at sample_a split_b then
                  match union_right_tree right_b with
                  | Empty => branch sample_b split_b left_b a
                  | right' => branch sample_b split_b left_b right'
                  end
                else
                  match union_right_tree left_b with
                  | Empty => branch sample_b split_b a right_b
                  | left' => branch sample_b split_b left' right_b
                  end
              else join a b
        end
  end.

Definition reuse_changed {A : Type} (original changed : t A) : t A :=
  match changed with
  | Empty => original
  | out => out
  end.

Definition union_left_specialized_changed_result {A : Type} (a b : t A) : t A :=
  reuse_changed a (union_left_specialized_changed a b).

(** Source model of the native [==] child-reuse decision.  The required
    refinement contract is only that a positive test implies lookup equality;
    native extraction will later instantiate this with physical identity. *)
Definition native_reuse_child {A : Type} (same : t A -> t A -> bool)
    (original changed : t A) : t A :=
  if same changed original then original else changed.

Definition native_reuse_same_branch {A : Type} (same : t A -> t A -> bool)
    (sample : string) (split : nat)
    (left_original right_original left_changed right_changed : t A) : t A :=
  Branch sample split
    (native_reuse_child same left_original left_changed)
    (native_reuse_child same right_original right_changed).

(** Compact unfolding rule for the changed worker.  Proofs use this instead
    of reducing the nested fixpoint, which would duplicate its local recursion
    at every occurrence. *)
Lemma union_left_specialized_changed_equation:
  forall (A : Type) (a b : t A),
    union_left_specialized_changed a b =
    match a, b with
    | Empty, tree => tree
    | _, Empty => Empty
    | Leaf ka va, Leaf kb _ =>
        if String.eqb ka kb then Empty else set ka va b
    | Leaf ka va, tree => set ka va tree
    | tree, Leaf kb vb =>
        match get kb tree with Some _ => Empty | None => set kb vb tree end
    | Branch sample_a split_a left_a right_a,
      Branch sample_b split_b left_b right_b =>
        if split_a =? split_b then
          if agrees_before_bounded sample_a sample_b split_a then
            match union_left_specialized_changed left_a left_b,
                  union_left_specialized_changed right_a right_b with
            | Empty, Empty => Empty
            | left', Empty => branch sample_a split_a left' right_a
            | Empty, right' => branch sample_a split_a left_a right'
            | left', right' => branch sample_a split_a left' right'
            end
          else join a b
        else if split_a <? split_b then
          if agrees_before_bounded sample_a sample_b split_a then
            if bit_at sample_b split_a then
              match union_left_specialized_changed right_a b with
              | Empty => Empty
              | right' => branch sample_a split_a left_a right'
              end
            else
              match union_left_specialized_changed left_a b with
              | Empty => Empty
              | left' => branch sample_a split_a left' right_a
              end
          else join a b
        else
          if agrees_before_bounded sample_a sample_b split_b then
            if bit_at sample_a split_b then
              match union_left_specialized_changed a right_b with
              | Empty => branch sample_b split_b left_b a
              | right' => branch sample_b split_b left_b right'
              end
            else
              match union_left_specialized_changed a left_b with
              | Empty => branch sample_b split_b a right_b
              | left' => branch sample_b split_b left' right_b
              end
          else join a b
    end.
Proof. intros A a b. destruct a; destruct b; reflexivity. Qed.

(** Compact proof-facing unfolding rule for the nested structural worker. *)
Lemma union_left_specialized_equation:
  forall (A : Type) (a b : t A),
    union_left_specialized a b =
    match a, b with
    | Empty, tree => tree
    | tree, Empty => tree
    | Leaf ka va, Leaf kb _ =>
        if String.eqb ka kb then a else set ka va b
    | Leaf ka va, tree => set ka va tree
    | tree, Leaf kb vb =>
        match get kb tree with Some _ => tree | None => set kb vb tree end
    | Branch sample_a split_a left_a right_a,
      Branch sample_b split_b left_b right_b =>
        if split_a =? split_b then
          if agrees_before_bounded sample_a sample_b split_a then
            branch sample_a split_a
              (union_left_specialized left_a left_b)
              (union_left_specialized right_a right_b)
          else join a b
        else if split_a <? split_b then
          if agrees_before_bounded sample_a sample_b split_a then
            if bit_at sample_b split_a then
              branch sample_a split_a left_a
                (union_left_specialized right_a b)
            else branch sample_a split_a
                (union_left_specialized left_a b) right_a
          else join a b
        else
          if agrees_before_bounded sample_a sample_b split_b then
            if bit_at sample_a split_b then
              branch sample_b split_b left_b
                (union_left_specialized a right_b)
            else branch sample_b split_b
                (union_left_specialized a left_b) right_b
          else join a b
    end.
Proof. intros A a b. destruct a; destruct b; reflexivity. Qed.

Definition union_right_specialized {A : Type} (a b : t A) : t A :=
  union_left_specialized b a.

Definition union_right_specialized_changed {A : Type} (a b : t A)
    : t A :=
  union_left_specialized_changed b a.

Definition union_right_specialized_changed_result {A : Type} (a b : t A) : t A :=
  union_left_specialized_changed_result b a.

(** Closure-free changed worker.  Recursion is directly on [fuel], so ordinary
    extraction emits one recursive function instead of a branch-local
    closure.  The structural bound is kept experimental until its companion
    refinement theorem equates it with the established nested worker. *)
Fixpoint union_left_specialized_changed_fuel {A : Type}
    (fuel : nat) (a b : t A) : t A :=
  match fuel with
  | O => Empty
  | S fuel' =>
      match a, b with
      | Empty, tree => tree
      | _, Empty => Empty
      | Leaf ka va, Leaf kb _ =>
          if String.eqb ka kb then Empty else set ka va b
      | Leaf ka va, tree => set ka va tree
      | tree, Leaf kb vb =>
          match get kb tree with Some _ => Empty | None => set kb vb tree end
      | Branch sample_a split_a left_a right_a,
        Branch sample_b split_b left_b right_b =>
          if split_a =? split_b then
            if agrees_before_bounded sample_a sample_b split_a then
              match union_left_specialized_changed_fuel fuel' left_a left_b,
                    union_left_specialized_changed_fuel fuel' right_a right_b with
              | Empty, Empty => Empty
              | left', Empty => branch sample_a split_a left' right_a
              | Empty, right' => branch sample_a split_a left_a right'
              | left', right' => branch sample_a split_a left' right'
              end
            else join a b
          else if split_a <? split_b then
            if agrees_before_bounded sample_a sample_b split_a then
              if bit_at sample_b split_a then
                match union_left_specialized_changed_fuel fuel' right_a b with
                | Empty => Empty
                | right' => branch sample_a split_a left_a right'
                end
              else
                match union_left_specialized_changed_fuel fuel' left_a b with
                | Empty => Empty
                | left' => branch sample_a split_a left' right_a
                end
            else join a b
          else
            if agrees_before_bounded sample_a sample_b split_b then
              if bit_at sample_a split_b then
                match union_left_specialized_changed_fuel fuel' a right_b with
                | Empty => branch sample_b split_b left_b a
                | right' => branch sample_b split_b left_b right'
                end
              else
                match union_left_specialized_changed_fuel fuel' a left_b with
                | Empty => branch sample_b split_b a right_b
                | left' => branch sample_b split_b left' right_b
                end
            else join a b
      end
  end.

Definition union_left_specialized_changed_fuel_result {A : Type} (a b : t A)
    : t A :=
  reuse_changed a
    (union_left_specialized_changed_fuel (S (size a + size b)) a b).
