(** Refinement theorems for the modeled compact-sequence backend.

    These theorems are about the Rocq [pseq] model.  They do not establish an
    OCaml array heap theorem; that remaining target obligation is recorded in
    the tracker. *)

From Stdlib Require Import List NArith RelationClasses SetoidList.

Require Import HashTableSpec HashTable HashTableBits HashTableNative HashTableProof.

Set Implicit Arguments.

Lemma native_get_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_get eqb fuel depth full_hash key native =
    get_tree eqb fuel depth full_hash key source.
Proof.
  intros K A eqb fuel depth full_hash key native source Hrefines.
  unfold native_refines in Hrefines. subst source.
  apply native_get_refines.
Qed.

Lemma native_set_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K) (value : A)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_refines (native_set eqb fuel depth full_hash key value native)
      (set_tree eqb fuel depth full_hash key value source).
Proof.
  intros K A eqb fuel depth full_hash key value native source Hrefines.
  unfold native_refines in *. subst source.
  apply native_set_refines.
Qed.

Lemma native_remove_refines_related :
  forall K A (eqb : K -> K -> bool) fuel depth full_hash (key : K)
         (native : native_tree K A) (source : tree K A),
    native_refines native source ->
    native_refines (native_remove eqb fuel depth full_hash key native)
      (remove_tree eqb fuel depth full_hash key source).
Proof.
  intros K A eqb fuel depth full_hash key native source Hrefines.
  unfold native_refines in *. subst source.
  apply native_remove_refines.
Qed.

Definition native_table_wf {K Seed A : Type} (E : K -> K -> Prop)
    (hash : Seed -> K -> N) (native : native_table K Seed A) : Prop :=
  table_wf E hash (source_table_of_native native).

Lemma native_table_wf_empty :
  forall K Seed A (E : K -> K -> Prop) (hash : Seed -> K -> N) (seed : Seed),
    native_table_wf E hash (@native_empty K Seed A seed).
Proof.
  intros. unfold native_table_wf. rewrite source_table_native_empty.
  apply table_wf_empty.
Qed.

Lemma native_table_wf_set :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_wf E hash (native_table_set eqb hash key value native).
Proof.
  intros K Seed A E hash eqb key value native Hequiv Heqb Hcongruent Hbound Hwf.
  change (table_wf E hash (source_table_of_native native)) in Hwf.
  change (table_wf E hash
    (source_table_of_native (native_table_set eqb hash key value native))).
  rewrite source_table_native_set.
  eapply table_wf_set; eauto.
Qed.

Lemma native_table_wf_remove :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    native_table_wf E hash (native_table_remove eqb hash key native).
Proof.
  intros K Seed A E hash eqb key native Hequiv Heqb Hcongruent Hwf.
  change (table_wf E hash (source_table_of_native native)) in Hwf.
  change (table_wf E hash
    (source_table_of_native (native_table_remove eqb hash key native))).
  rewrite source_table_native_remove.
  eapply table_wf_remove; eauto.
Qed.

Lemma native_table_get_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_get eqb hash key (native_table_set eqb hash key value native) =
    Some value.
Proof.
  intros K Seed A E hash eqb key value native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_get_refines, source_table_native_set.
  eapply get_after_set_self; eauto.
Qed.

Lemma native_table_mem_after_set_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_mem eqb hash key (native_table_set eqb hash key value native) = true.
Proof.
  intros K Seed A E hash eqb key value native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_mem_refines, source_table_native_set.
  eapply mem_after_set_self; eauto.
Qed.

Lemma native_table_get_after_remove_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    native_table_get eqb hash key (native_table_remove eqb hash key native) = None.
Proof.
  intros K Seed A E hash eqb key native Hequiv Heqb Hcongruent Hwf.
  rewrite native_table_get_refines, source_table_native_remove.
  eapply get_after_remove_self; eauto.
Qed.

Lemma native_table_mem_after_remove_self :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    native_table_mem eqb hash key (native_table_remove eqb hash key native) = false.
Proof.
  intros K Seed A E hash eqb key native Hequiv Heqb Hcongruent Hwf.
  rewrite native_table_mem_refines, source_table_native_remove.
  eapply mem_after_remove_self; eauto.
Qed.

Lemma native_table_get_after_set_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_get eqb hash query (native_table_set eqb hash key value native) =
    Some value.
Proof.
  intros K Seed A E hash eqb query key value native Hequiv Heqb Hcongruent
    Hrelated Hbound Hwf.
  rewrite native_table_get_refines, source_table_native_set.
  eapply get_after_set_equiv; eauto.
Qed.

Lemma native_table_mem_after_set_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    (hash (native_table_seed native) key < hash_space)%N ->
    native_table_wf E hash native ->
    native_table_mem eqb hash query (native_table_set eqb hash key value native) = true.
Proof.
  intros K Seed A E hash eqb query key value native Hequiv Heqb Hcongruent
    Hrelated Hbound Hwf.
  rewrite native_table_mem_refines, source_table_native_set.
  eapply mem_after_set_equiv; eauto.
Qed.

Lemma native_table_get_after_remove_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    native_table_wf E hash native ->
    native_table_get eqb hash query (native_table_remove eqb hash key native) = None.
Proof.
  intros K Seed A E hash eqb query key native Hequiv Heqb Hcongruent Hrelated Hwf.
  rewrite native_table_get_refines, source_table_native_remove.
  eapply get_after_remove_equiv; eauto.
Qed.

Lemma native_table_mem_after_remove_equiv :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (query key : K) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    E query key ->
    native_table_wf E hash native ->
    native_table_mem eqb hash query (native_table_remove eqb hash key native) = false.
Proof.
  intros K Seed A E hash eqb query key native Hequiv Heqb Hcongruent Hrelated Hwf.
  rewrite native_table_mem_refines, source_table_native_remove.
  eapply mem_after_remove_equiv; eauto.
Qed.

Lemma native_table_get_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query (value : A)
         (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) query < hash_space)%N ->
    native_table_wf E hash native ->
    (native_table_get eqb hash query native = Some value <->
      exists stored,
        In (stored, value) (native_table_elements native) /\ E query stored).
Proof.
  intros K Seed A E hash eqb query value native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_get_refines, native_table_elements_refines.
  eapply get_binding_iff; eauto.
Qed.

Lemma native_table_mem_binding_iff :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) query (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    (hash (native_table_seed native) query < hash_space)%N ->
    native_table_wf E hash native ->
    (native_table_mem eqb hash query native = true <->
      exists stored value,
        In (stored, value) (native_table_elements native) /\ E query stored).
Proof.
  intros K Seed A E hash eqb query native Hequiv Heqb Hcongruent Hbound Hwf.
  rewrite native_table_mem_refines, native_table_elements_refines.
  eapply mem_binding_iff; eauto.
Qed.

Lemma native_table_elements_keys_nodup :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (native : native_table K Seed A),
    native_table_wf E hash native ->
    NoDupA E (map fst (native_table_elements native)).
Proof.
  intros K Seed A E hash native Hwf.
  rewrite native_table_elements_refines.
  apply (@elements_keys_nodup K Seed A E hash (source_table_of_native native)).
  exact Hwf.
Qed.

Lemma native_table_is_empty_iff_get_none :
  forall (K Seed A : Type) (E : K -> K -> Prop) (hash : Seed -> K -> N)
         (eqb : K -> K -> bool) (native : native_table K Seed A),
    Equivalence E ->
    (forall first second, eqb first second = true <-> E first second) ->
    (forall seed first second, E first second ->
      hash seed first = hash seed second) ->
    native_table_wf E hash native ->
    (native_table_is_empty native = true <->
      forall query, native_table_get eqb hash query native = None).
Proof.
  intros K Seed A E hash eqb native Hequiv Heqb Hcongruent Hwf.
  rewrite native_table_is_empty_refines.
  rewrite (@is_empty_iff_get_none K Seed A E eqb hash
    (source_table_of_native native) Hequiv Heqb Hcongruent Hwf).
  split; intros Hall query.
  - rewrite native_table_get_refines. apply Hall.
  - rewrite <- native_table_get_refines. apply Hall.
Qed.
