(** Contracts shared by the persistent hash-table development.

    Hashes route through a fixed 30-bit domain.  Raw target hashes are signed
    integers because OCaml [int] values may be negative; [normalize_hash]
    models the wrapper's low-30-bit adaptation before a hash reaches a tree.
    The generic map proofs take their equality and hash laws as ordinary
    hypotheses, so this file introduces no global axioms. *)

From Stdlib Require Import Bool Lia List NArith ZArith Strings.String.
Import ListNotations.

Set Implicit Arguments.

Definition hash_bits : N := 30%N.
Definition hash_space : N := 1073741824%N. (* 2^30 *)
Definition hash_mask : N := 1073741823%N.  (* 2^30 - 1 *)
Definition hash_modulus : Z := 1073741824%Z.

Definition normalize_hash (raw : Z) : N :=
  Z.to_N (raw mod hash_modulus).

Lemma hash_space_positive : (0 < hash_space)%N.
Proof. now vm_compute. Qed.

Lemma hash_modulus_positive : (0 < hash_modulus)%Z.
Proof. now vm_compute. Qed.

Lemma normalize_hash_bound :
  forall raw, (normalize_hash raw < hash_space)%N.
Proof.
  intro raw.
  unfold normalize_hash, hash_space, hash_modulus.
  change (Z.to_N (raw mod 1073741824) < Z.to_N 1073741824)%N.
  pose proof (Z.mod_pos_bound raw 1073741824 ltac:(lia)) as Hmod.
  destruct Hmod as [Hnonneg Hbound].
  refine (proj1 (Z2N.inj_lt _ _ Hnonneg _) Hbound).
  lia.
Qed.

Lemma normalize_hash_nonnegative_raw :
  forall raw,
    (0 <= raw < hash_modulus)%Z ->
    normalize_hash raw = Z.to_N raw.
Proof.
  intros raw Hraw.
  unfold normalize_hash.
  rewrite Z.mod_small by exact Hraw.
  reflexivity.
Qed.

(** These boundary calculations model OCaml's [(land 0x3fffffff)] behavior
    for the signed raw hashes that most often expose a mistaken unsigned-only
    normalization. *)
Lemma normalize_hash_negative_one : normalize_hash (-1) = hash_mask.
Proof. now vm_compute. Qed.

Lemma normalize_hash_negative_modulus :
  normalize_hash (- hash_modulus) = 0%N.
Proof. now vm_compute. Qed.

(** A key package is represented explicitly rather than as a global type
    class.  This makes each theorem's callback obligations visible and lets
    several lawful key packages coexist in one development. *)
Record KeyContract : Type := {
  key_type : Type;
  key_equiv : key_type -> key_type -> Prop;
  key_eqb : key_type -> key_type -> bool;
  key_equiv_refl : forall k, key_equiv k k;
  key_equiv_sym : forall k q, key_equiv k q -> key_equiv q k;
  key_equiv_trans : forall k q r,
      key_equiv k q -> key_equiv q r -> key_equiv k r;
  key_eqb_spec : forall k q, key_eqb k q = true <-> key_equiv k q
}.

Definition HashContract (K : KeyContract) (Seed : Type) : Type :=
  { hash : Seed -> key_type K -> N |
    forall seed k, (hash seed k < hash_space)%N }.

Definition hash_congruent (K : KeyContract) (Seed : Type)
    (h : Seed -> key_type K -> N) : Prop :=
  forall seed k q, key_equiv K k q -> h seed k = h seed q.

Section Instances.

  Definition z_key_contract : KeyContract.
  Proof.
    refine {| key_type := Z;
              key_equiv := eq;
              key_eqb := Z.eqb |}.
    - exact (fun k => eq_refl).
    - intros x y H. now symmetry.
    - intros x y z Hxy Hyz. now transitivity y.
    - exact Z.eqb_eq.
  Defined.

  Definition z_hash (_ : unit) (k : Z) : N := normalize_hash k.

  Lemma z_hash_bound : forall seed k, (z_hash seed k < hash_space)%N.
  Proof. exact (fun _ => normalize_hash_bound). Qed.

  Lemma z_hash_congruent : @hash_congruent z_key_contract unit z_hash.
  Proof. intros ? ? ? ->; reflexivity. Qed.

  Definition string_key_contract : KeyContract.
  Proof.
    refine {| key_type := string;
              key_equiv := eq;
              key_eqb := String.eqb |}.
    - exact (fun k => eq_refl).
    - intros x y H. now symmetry.
    - intros x y z Hxy Hyz. now transitivity y.
    - exact String.eqb_eq.
  Defined.

  (** This deliberately simple executable instance is a pure test hash.  The
      public OCaml string adapter later supplies [Hashtbl.seeded_hash] and
      documents its separate foreign contract. *)
  Definition string_test_hash (_ : unit) (_ : string) : N := 0%N.

  Lemma string_test_hash_bound :
    forall seed k, (string_test_hash seed k < hash_space)%N.
  Proof. intros; apply hash_space_positive. Qed.

  Lemma string_test_hash_congruent :
    @hash_congruent string_key_contract unit string_test_hash.
  Proof. intros ? ? ? _; reflexivity. Qed.

  Record record_key : Type := {
    record_id : Z;
    record_label : string
  }.

  Definition record_equiv (x y : record_key) : Prop :=
    record_id x = record_id y.

  Definition record_eqb (x y : record_key) : bool :=
    Z.eqb (record_id x) (record_id y).

  Definition record_key_contract : KeyContract.
  Proof.
    refine {| key_type := record_key;
              key_equiv := record_equiv;
              key_eqb := record_eqb |}.
    - intros [id label]. reflexivity.
    - intros [xid xlabel] [yid ylabel] H. now symmetry.
    - intros [xid xlabel] [yid ylabel] [zid zlabel] Hxy Hyz.
      now transitivity yid.
    - intros [xid xlabel] [yid ylabel].
      unfold record_eqb, record_equiv. simpl. apply Z.eqb_eq.
  Defined.

  Definition record_hash (_ : unit) (k : record_key) : N :=
    normalize_hash (record_id k).

  Lemma record_hash_bound :
    forall seed k, (record_hash seed k < hash_space)%N.
  Proof.
    intros seed [id label]. exact (normalize_hash_bound id).
  Qed.

  Lemma record_hash_congruent :
    @hash_congruent record_key_contract unit record_hash.
  Proof.
    intros seed [xid xlabel] [yid ylabel] Heq.
    change (xid = yid)%Z in Heq.
    subst yid. reflexivity.
  Qed.

End Instances.
