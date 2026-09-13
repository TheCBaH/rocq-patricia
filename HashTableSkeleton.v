(** Strictly-positive, executable H0 prototype for the future HAMT.

    This is deliberately not the final routing algorithm.  It fixes the
    source shape used by H1/H2: children are an ordinary positive list of
    nodes, and all non-structural recursion consumes an explicit six-level
    budget.  The final bitmap/rank implementation will refine this shape.
    No axiom or extraction override is used here. *)

From Stdlib Require Import Bool List NArith.
Import ListNotations.

Require Import HashTableSpec.

Set Implicit Arguments.

Inductive node (K A : Type) : Type :=
| NodeEmpty
| NodeLeaf (full_hash : N) (key : K) (value : A)
| NodeCollision (full_hash : N) (entries : list (K * A))
| NodeBranch (children : list (node K A)).

Arguments NodeEmpty {K A}.
Arguments NodeLeaf {K A} _ _ _.
Arguments NodeCollision {K A} _ _.
Arguments NodeBranch {K A} _.

Definition prototype_depth : nat := 6.

Definition slot (full_hash : N) (depth : nat) : N :=
  N.land (N.shiftr full_hash (N.of_nat (5 * depth))) 31%N.

Fixpoint join_worker {K A : Type} (fuel : nat)
    (left_hash : N) (left : node K A)
    (right_hash : N) (right : node K A) : node K A :=
  match fuel with
  | O => NodeBranch [left; right]
  | S fuel' =>
      if N.eqb (slot left_hash fuel') (slot right_hash fuel')
      then NodeBranch [join_worker fuel' left_hash left right_hash right]
      else NodeBranch [left; right]
  end.

Fixpoint update_worker {K A : Type} (eqb : K -> K -> bool)
    (fuel : nat) (full_hash : N) (key : K) (value : A)
    (tree : node K A) : node K A :=
  match tree with
  | NodeEmpty => NodeLeaf full_hash key value
  | NodeLeaf old_hash old_key old_value =>
      if eqb key old_key
      then NodeLeaf old_hash old_key value
      else join_worker fuel full_hash (NodeLeaf full_hash key value)
             old_hash (NodeLeaf old_hash old_key old_value)
  | NodeCollision old_hash entries =>
      NodeCollision old_hash ((key, value) :: entries)
  | NodeBranch children =>
      match fuel, children with
      | O, _ => tree
      | S fuel', [] => NodeBranch [NodeLeaf full_hash key value]
      | S fuel', child :: rest =>
          NodeBranch (update_worker eqb fuel' full_hash key value child :: rest)
      end
  end.

Definition prototype_set {K A : Type} (eqb : K -> K -> bool)
    (full_hash : N) (key : K) (value : A) (tree : node K A) : node K A :=
  update_worker eqb prototype_depth full_hash key value tree.

Lemma join_worker_depth_zero :
  forall K A (left right : node K A) left_hash right_hash,
    join_worker 0 left_hash left right_hash right = NodeBranch [left; right].
Proof. reflexivity. Qed.

Lemma prototype_set_empty :
  forall K A eqb full_hash (key : K) (value : A),
    prototype_set eqb full_hash key value NodeEmpty = NodeLeaf full_hash key value.
Proof. reflexivity. Qed.
