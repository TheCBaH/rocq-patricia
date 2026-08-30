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
