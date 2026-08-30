(** Focused certificates and refinement proof workspace for
    [PatriciaUnion].  Recompiling this file reuses the cached core proof. *)

From Stdlib Require Import Bool NArith.
Require Import PatriciaBits Patricia PatriciaProof PatriciaUnion.

Theorem union_left_specialized_empty_right:
  forall (A : Type) (left : t A),
    union_left_specialized left Empty = left.
Proof. intros A left. destruct left; reflexivity. Qed.

Theorem union_left_specialized_empty_left:
  forall (A : Type) (right : t A),
    union_left_specialized Empty right = right.
Proof. reflexivity. Qed.

Theorem union_left_specialized_disjoint_masks:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    (N.eqb ma mb && N.eqb pa pb)%bool = false ->
    mask_above ma mb = false ->
    mask_above mb ma = false ->
    union_left_specialized (Branch pa ma la ra) (Branch pb mb lb rb) =
    join (Branch pa ma la ra) (Branch pb mb lb rb).
Proof.
  intros A pa ma la ra pb mb lb rb Hsame Hab Hba.
  cbn [union_left_specialized]. rewrite Hsame, Hab, Hba. reflexivity.
Qed.
