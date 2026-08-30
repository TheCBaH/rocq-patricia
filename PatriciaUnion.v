(** Experimental source counterpart of the optimized integer biased union.
    This companion module deliberately keeps worker iteration out of the
    established [Patricia.v]/[PatriciaProof.v] closure. *)

From Stdlib Require Import Bool NArith PArith.
Require Import PatriciaBits Patricia.

Fixpoint union_left_specialized {A : Type} (a : t A) {struct a}
    : t A -> t A :=
  match a with
  | Empty => fun b => b
  | Leaf ka va => fun b =>
      match b with
      | Empty => a
      | Leaf kb _ => if Pos.eqb ka kb then a else set ka va b
      | Branch _ _ _ _ => set ka va b
      end
  | Branch pa ma la ra =>
      fix union_right_tree (b : t A) {struct b} : t A :=
        match b with
        | Empty => a
        | Leaf kb vb =>
            match get kb a with Some _ => a | None => set kb vb a end
        | Branch pb mb lb rb =>
            if (N.eqb ma mb && N.eqb pa pb)%bool then
              branch pa ma
                (union_left_specialized la lb)
                (union_left_specialized ra rb)
            else if mask_above ma mb then
              match representative b with
              | Some kb =>
                  if matches_prefix kb pa ma then
                    if zero_bit kb ma then
                      branch pa ma (union_left_specialized la b) ra
                    else branch pa ma la (union_left_specialized ra b)
                  else join a b
              | None => a
              end
            else if mask_above mb ma then
              match representative a with
              | Some ka =>
                  if matches_prefix ka pb mb then
                    if zero_bit ka mb then
                      branch pb mb (union_right_tree lb) rb
                    else branch pb mb lb (union_right_tree rb)
                  else join a b
              | None => b
              end
            else join a b
        end
  end.

(** A source-level change signal for the sharing optimization.  [None] means
    that the left-biased union has exactly the original left tree as its
    result; [Some out] carries the rebuilt result otherwise.  Unlike OCaml
    physical equality, this is ordinary data in the source semantics and can
    therefore receive a refinement proof. *)
Fixpoint union_left_specialized_changed {A : Type} (a : t A) {struct a}
    : t A -> option (t A) :=
  match a with
  | Empty => fun b =>
      match b with Empty => None | _ => Some b end
  | Leaf ka va => fun b =>
      match b with
      | Empty => None
      | Leaf kb _ => if Pos.eqb ka kb then None else Some (set ka va b)
      | Branch _ _ _ _ => Some (set ka va b)
      end
  | Branch pa ma la ra =>
      fix union_right_tree (b : t A) {struct b} : option (t A) :=
        match b with
        | Empty => None
        | Leaf kb vb =>
            match get kb a with Some _ => None | None => Some (set kb vb a) end
        | Branch pb mb lb rb =>
            if (N.eqb ma mb && N.eqb pa pb)%bool then
              match union_left_specialized_changed la lb,
                    union_left_specialized_changed ra rb with
              | None, None => None
              | Some left', None => Some (branch pa ma left' ra)
              | None, Some right' => Some (branch pa ma la right')
              | Some left', Some right' => Some (branch pa ma left' right')
              end
            else if mask_above ma mb then
              match representative b with
              | Some kb =>
                  if matches_prefix kb pa ma then
                    if zero_bit kb ma then
                      match union_left_specialized_changed la b with
                      | None => None
                      | Some left' => Some (branch pa ma left' ra)
                      end
                    else
                      match union_left_specialized_changed ra b with
                      | None => None
                      | Some right' => Some (branch pa ma la right')
                      end
                  else Some (join a b)
              | None => None
              end
            else if mask_above mb ma then
              match representative a with
              | Some ka =>
                  if matches_prefix ka pb mb then
                    if zero_bit ka mb then
                      match union_right_tree lb with
                      | None => Some (branch pb mb a rb)
                      | Some left' => Some (branch pb mb left' rb)
                      end
                    else
                      match union_right_tree rb with
                      | None => Some (branch pb mb lb a)
                      | Some right' => Some (branch pb mb lb right')
                      end
                  else Some (join a b)
              | None => Some b
              end
            else Some (join a b)
        end
  end.

Definition union_left_specialized_changed_result {A : Type} (a b : t A) : t A :=
  match union_left_specialized_changed a b with
  | None => a
  | Some out => out
  end.

(** One-step equation for changed-result refinement proofs. *)
Lemma union_left_specialized_changed_equation:
  forall (A : Type) (a b : t A),
    union_left_specialized_changed a b =
    match a, b with
    | Empty, Empty => None
    | Empty, tree => Some tree
    | _, Empty => None
    | Leaf ka va, Leaf kb _ =>
        if Pos.eqb ka kb then None else Some (set ka va b)
    | Leaf ka va, tree => Some (set ka va tree)
    | tree, Leaf kb vb =>
        match get kb tree with Some _ => None | None => Some (set kb vb tree) end
    | Branch pa ma la ra, Branch pb mb lb rb =>
        if (N.eqb ma mb && N.eqb pa pb)%bool then
          match union_left_specialized_changed la lb,
                union_left_specialized_changed ra rb with
          | None, None => None
          | Some left', None => Some (branch pa ma left' ra)
          | None, Some right' => Some (branch pa ma la right')
          | Some left', Some right' => Some (branch pa ma left' right')
          end
        else if mask_above ma mb then
          match representative b with
          | Some kb =>
              if matches_prefix kb pa ma then
                if zero_bit kb ma then
                  match union_left_specialized_changed la b with
                  | None => None
                  | Some left' => Some (branch pa ma left' ra)
                  end
                else
                  match union_left_specialized_changed ra b with
                  | None => None
                  | Some right' => Some (branch pa ma la right')
                  end
              else Some (join a b)
          | None => None
          end
        else if mask_above mb ma then
          match representative a with
          | Some ka =>
              if matches_prefix ka pb mb then
                if zero_bit ka mb then
                  match union_left_specialized_changed a lb with
                  | None => Some (branch pb mb a rb)
                  | Some left' => Some (branch pb mb left' rb)
                  end
                else
                  match union_left_specialized_changed a rb with
                  | None => Some (branch pb mb lb a)
                  | Some right' => Some (branch pb mb lb right')
                  end
              else Some (join a b)
          | None => Some b
          end
        else Some (join a b)
    end.
Proof. intros A a b. destruct a; destruct b; reflexivity. Qed.

(** Two-argument unfolding rule for proofs.  It hides whether a recursive
    call is implemented by the outer or the local structural fixpoint. *)
Lemma union_left_specialized_equation:
  forall (A : Type) (a b : t A),
    union_left_specialized a b =
    match a, b with
    | Empty, tree => tree
    | tree, Empty => tree
    | Leaf ka va, Leaf kb _ =>
        if Pos.eqb ka kb then a else set ka va b
    | Leaf ka va, tree => set ka va tree
    | tree, Leaf kb vb =>
        match get kb tree with Some _ => tree | None => set kb vb tree end
    | Branch pa ma la ra, Branch pb mb lb rb =>
        if (N.eqb ma mb && N.eqb pa pb)%bool then
          branch pa ma
            (union_left_specialized la lb)
            (union_left_specialized ra rb)
        else if mask_above ma mb then
          match representative b with
          | Some kb =>
              if matches_prefix kb pa ma then
                if zero_bit kb ma then
                  branch pa ma (union_left_specialized la b) ra
                else branch pa ma la (union_left_specialized ra b)
              else join a b
          | None => a
          end
        else if mask_above mb ma then
          match representative a with
          | Some ka =>
              if matches_prefix ka pb mb then
                if zero_bit ka mb then
                  branch pb mb (union_left_specialized a lb) rb
                else branch pb mb lb (union_left_specialized a rb)
              else join a b
          | None => b
          end
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
