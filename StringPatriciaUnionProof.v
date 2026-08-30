(** Focused certificates and refinement proof workspace for the specialized
    direct-string union worker. *)

From Stdlib Require Import PeanoNat Strings.String.
Require Import StringBits StringPatricia StringPatriciaProof StringPatriciaUnion.

Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros A left. destruct left; reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. reflexivity. Qed.

Theorem union_left_specialized_disjoint_samples:
  forall (A : Type) sample_a split (left_a right_a : t A)
      sample_b (left_b right_b : t A),
    agrees_before_bounded sample_a sample_b split = false ->
    union_left_specialized
      (Branch sample_a split left_a right_a)
      (Branch sample_b split left_b right_b) =
    join (Branch sample_a split left_a right_a)
      (Branch sample_b split left_b right_b).
Proof.
  intros A sample_a split left_a right_a sample_b left_b right_b Hagree.
  cbn [union_left_specialized]. rewrite Nat.eqb_refl, Hagree. reflexivity.
Qed.
