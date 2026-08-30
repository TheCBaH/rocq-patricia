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

(** Source-visible changed-result worker.  A [None] result is a certificate
    that the caller can reuse its original left tree directly after ordinary
    extraction, without an OCaml physical-equality test. *)
Fixpoint union_left_specialized_changed {A : Type} (a : t A) {struct a}
    : t A -> option (t A) :=
  match a with
  | Empty => fun b =>
      match b with Empty => None | _ => Some b end
  | Leaf ka va => fun b =>
      match b with
      | Empty => None
      | Leaf kb _ => if String.eqb ka kb then None else Some (set ka va b)
      | Branch _ _ _ _ => Some (set ka va b)
      end
  | Branch sample_a split_a left_a right_a =>
      fix union_right_tree (b : t A) {struct b} : option (t A) :=
        match b with
        | Empty => None
        | Leaf kb vb =>
            match get kb a with Some _ => None | None => Some (set kb vb a) end
        | Branch sample_b split_b left_b right_b =>
            if split_a =? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                match union_left_specialized_changed left_a left_b,
                      union_left_specialized_changed right_a right_b with
                | None, None => None
                | Some left', None => Some (branch sample_a split_a left' right_a)
                | None, Some right' => Some (branch sample_a split_a left_a right')
                | Some left', Some right' => Some (branch sample_a split_a left' right')
                end
              else Some (join a b)
            else if split_a <? split_b then
              if agrees_before_bounded sample_a sample_b split_a then
                if bit_at sample_b split_a then
                  match union_left_specialized_changed right_a b with
                  | None => None
                  | Some right' => Some (branch sample_a split_a left_a right')
                  end
                else
                  match union_left_specialized_changed left_a b with
                  | None => None
                  | Some left' => Some (branch sample_a split_a left' right_a)
                  end
              else Some (join a b)
            else
              if agrees_before_bounded sample_a sample_b split_b then
                if bit_at sample_a split_b then
                  match union_right_tree right_b with
                  | None => None
                  | Some right' => Some (branch sample_b split_b left_b right')
                  end
                else
                  match union_right_tree left_b with
                  | None => None
                  | Some left' => Some (branch sample_b split_b left' right_b)
                  end
              else Some (join a b)
        end
  end.

Definition union_left_specialized_changed_result {A : Type} (a b : t A) : t A :=
  match union_left_specialized_changed a b with
  | None => a
  | Some out => out
  end.

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
    : option (t A) :=
  union_left_specialized_changed b a.

Definition union_right_specialized_changed_result {A : Type} (a b : t A) : t A :=
  union_left_specialized_changed_result b a.
