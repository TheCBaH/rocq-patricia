(** A minimal heap-identity bridge for the specialized native unions.

    OCaml's [(==)] is outside Rocq's semantics.  This file isolates the exact
    foreign-interface obligation needed to connect it to the source proofs:
    a current runtime tree root has a heap location, a location denotes one
    source tree, and a successful physical test denotes equal locations.

    The model deliberately does not claim that OCaml implements these
    hypotheses.  Establishing that connection requires an OCaml heap/compiler
    semantics.  What is kernel-checked here is that the hypotheses are enough
    to discharge the [native_same_sound] premise used by both union proofs. *)

From Stdlib Require Import Bool PeanoNat.
Require Import Patricia PatriciaUnionProof StringPatricia StringPatriciaUnionProof.

Definition heap_location := nat.

Definition physical_same (left right : heap_location) : bool :=
  Nat.eqb left right.

(** [heap_view] is the current immutable-tree view of the runtime heap.  It
    is intentionally total: locations outside the implementation's allocated
    domain may be assigned an arbitrary view, because the FFI contract below
    quantifies only over locations that represent actual inputs. *)
Definition represents {Tree : Type}
    (heap_view : heap_location -> Tree) (tree : Tree) (root : heap_location) : Prop :=
  heap_view root = tree.

(** Target-level contract for the extracted [(==)] callback.  It is only a
    positive-direction contract: a false result may merely cause rebuilding.
    The two witnesses are allowed to differ syntactically before
    [physical_same] identifies them, which makes the heap part of the
    assumption explicit rather than conflating it with source-tree equality. *)
Definition same_realizes_physical {Tree : Type}
    (heap_view : heap_location -> Tree) (same : Tree -> Tree -> bool) : Prop :=
  forall changed original,
    same changed original = true ->
    exists changed_root original_root,
      represents heap_view changed changed_root /\
      represents heap_view original original_root /\
      physical_same changed_root original_root = true.

Lemma physical_same_represents_equal:
  forall (Tree : Type) (heap_view : heap_location -> Tree)
      changed original changed_root original_root,
    represents heap_view changed changed_root ->
    represents heap_view original original_root ->
    physical_same changed_root original_root = true ->
    changed = original.
Proof.
  intros Tree heap_view changed original changed_root original_root
    Hchanged Horiginal Hsame.
  unfold physical_same in Hsame. apply Nat.eqb_eq in Hsame. subst original_root.
  unfold represents in Hchanged, Horiginal.
  rewrite <- Hchanged. exact Horiginal.
Qed.

Lemma same_realizes_physical_sound:
  forall (Tree : Type) (heap_view : heap_location -> Tree)
      (same : Tree -> Tree -> bool),
    same_realizes_physical heap_view same ->
    forall changed original,
      same changed original = true -> changed = original.
Proof.
  intros Tree heap_view same Hrealizes changed original Hsame.
  destruct (Hrealizes changed original Hsame)
    as [changed_root [original_root [Hchanged [Horiginal Hroots]]]].
  eapply physical_same_represents_equal; eauto.
Qed.

Theorem patricia_heap_same_sound:
  forall (A : Type) (heap_view : heap_location -> Patricia.t A)
      (same : Patricia.t A -> Patricia.t A -> bool),
    same_realizes_physical heap_view same ->
    PatriciaUnionProof.native_same_sound same.
Proof.
  intros A heap_view same Hrealizes changed original Hsame.
  pose proof (same_realizes_physical_sound (Patricia.t A) heap_view same
    Hrealizes changed original Hsame) as Htrees.
  subst original. apply PatriciaProof.equiv_refl.
Qed.

Theorem string_patricia_heap_same_sound:
  forall (A : Type) (heap_view : heap_location -> StringPatricia.t A)
      (same : StringPatricia.t A -> StringPatricia.t A -> bool),
    same_realizes_physical heap_view same ->
    StringPatriciaUnionProof.native_same_sound same.
Proof.
  intros A heap_view same Hrealizes changed original Hsame.
  pose proof (same_realizes_physical_sound (StringPatricia.t A) heap_view same
    Hrealizes changed original Hsame) as Htrees.
  subst original. apply StringPatriciaProof.equiv_refl.
Qed.

(** The preceding bridge treats every input as an allocated root.  OCaml also
    represents nullary constructors immediately, so make that runtime case
    explicit.  This is the smallest value/heap semantics needed by the union
    code: it never inspects pointers, allocates, mutates, or compares payloads;
    it only asks whether two current tree roots are physically the same. *)
Inductive runtime_root : Type :=
| Immediate_empty
| Allocated_root (location : heap_location).

Definition runtime_same (left right : runtime_root) : bool :=
  match left, right with
  | Immediate_empty, Immediate_empty => true
  | Allocated_root left_location, Allocated_root right_location =>
      physical_same left_location right_location
  | _, _ => false
  end.

Definition root_represents {Tree : Type}
    (empty : Tree) (heap_view : heap_location -> Tree)
    (root : runtime_root) (tree : Tree) : Prop :=
  match root with
  | Immediate_empty => tree = empty
  | Allocated_root location => heap_view location = tree
  end.

Definition same_realizes_runtime {Tree : Type}
    (empty : Tree) (heap_view : heap_location -> Tree)
    (same : Tree -> Tree -> bool) : Prop :=
  forall changed original,
    same changed original = true ->
    exists changed_root original_root,
      root_represents empty heap_view changed_root changed /\
      root_represents empty heap_view original_root original /\
      runtime_same changed_root original_root = true.

Lemma runtime_same_represents_equal:
  forall (Tree : Type) (empty : Tree) (heap_view : heap_location -> Tree)
      changed original changed_root original_root,
    root_represents empty heap_view changed_root changed ->
    root_represents empty heap_view original_root original ->
    runtime_same changed_root original_root = true ->
    changed = original.
Proof.
  intros Tree empty heap_view changed original changed_root original_root
    Hchanged Horiginal Hsame.
  destruct changed_root, original_root; cbn in Hchanged, Horiginal, Hsame.
  - now rewrite Hchanged, Horiginal.
  - discriminate.
  - discriminate.
  - eapply physical_same_represents_equal; eauto.
Qed.

Lemma same_realizes_runtime_sound:
  forall (Tree : Type) (empty : Tree) (heap_view : heap_location -> Tree)
      (same : Tree -> Tree -> bool),
    same_realizes_runtime empty heap_view same ->
    forall changed original,
      same changed original = true -> changed = original.
Proof.
  intros Tree empty heap_view same Hrealizes changed original Hsame.
  destruct (Hrealizes changed original Hsame)
    as [changed_root [original_root [Hchanged [Horiginal Hroots]]]].
  eapply runtime_same_represents_equal; eauto.
Qed.

Theorem patricia_runtime_same_sound:
  forall (A : Type) (heap_view : heap_location -> Patricia.t A)
      (same : Patricia.t A -> Patricia.t A -> bool),
    same_realizes_runtime Patricia.Empty heap_view same ->
    PatriciaUnionProof.native_same_sound same.
Proof.
  intros A heap_view same Hrealizes changed original Hsame.
  pose proof (same_realizes_runtime_sound (Patricia.t A) Patricia.Empty
    heap_view same Hrealizes changed original Hsame) as Htrees.
  subst original. apply PatriciaProof.equiv_refl.
Qed.

Theorem string_patricia_runtime_same_sound:
  forall (A : Type) (heap_view : heap_location -> StringPatricia.t A)
      (same : StringPatricia.t A -> StringPatricia.t A -> bool),
    same_realizes_runtime StringPatricia.Empty heap_view same ->
    StringPatriciaUnionProof.native_same_sound same.
Proof.
  intros A heap_view same Hrealizes changed original Hsame.
  pose proof (same_realizes_runtime_sound (StringPatricia.t A)
    StringPatricia.Empty heap_view same Hrealizes changed original Hsame) as Htrees.
  subst original. apply StringPatriciaProof.equiv_refl.
Qed.

(** ** OCaml-object refinement boundary

    The preceding contract is deliberately phrased only in terms of source
    trees.  The target-language statement has one more layer: an executing
    tree value carries both a source interpretation and the OCaml word at
    which that interpretation currently resides.  Making that layer explicit
    prevents an external proof from silently treating a source tree as though
    it had a canonical heap address.  Equal source trees may, of course, be
    represented by distinct OCaml blocks; this is why the model requires only
    the positive direction of physical equality. *)

(** A current heap has an allocated domain as well as contents.  The old
    total [heap_view] remains convenient for the source bridge above; its
    values outside [heap_allocated] are intentionally irrelevant here. *)
Record heap_state (Tree : Type) : Type := {
  heap_allocated : heap_location -> Prop;
  heap_contents : heap_location -> Tree
}.

Definition state_root_represents {Tree : Type} (state : heap_state Tree)
    (empty : Tree) (root : runtime_root) (tree : Tree) : Prop :=
  match root with
  | Immediate_empty => tree = empty
  | Allocated_root location =>
      @heap_allocated Tree state location /\
      @heap_contents Tree state location = tree
  end.

(** A [tree_object] is an OCaml value together with its current source-tree
    interpretation.  This is the relation an external OCaml heap semantics
    must establish for values passed to the handwritten union worker. *)
Record tree_object {Tree : Type} (state : heap_state Tree) (empty : Tree) : Type := {
  object_root : runtime_root;
  object_tree : Tree;
  object_represents : state_root_represents state empty object_root object_tree
}.

Definition ocaml_physical_equal {Tree : Type} {state : heap_state Tree}
    {empty : Tree} (left right : tree_object state empty) : bool :=
  runtime_same (@object_root Tree state empty left)
    (@object_root Tree state empty right).

Lemma state_root_represents_forgets_allocation:
  forall (Tree : Type) (state : heap_state Tree) (empty tree : Tree) root,
    state_root_represents state empty root tree ->
    root_represents empty (@heap_contents Tree state) root tree.
Proof.
  intros Tree state empty tree root Hrep.
  destruct root; cbn in Hrep |- *.
  - exact Hrep.
  - exact (proj2 Hrep).
Qed.

Lemma ocaml_physical_equal_sound:
  forall (Tree : Type) (state : heap_state Tree) (empty : Tree)
      (changed original : tree_object state empty),
    ocaml_physical_equal changed original = true ->
    @object_tree Tree state empty changed = @object_tree Tree state empty original.
Proof.
  intros Tree state empty changed original Hsame.
  unfold ocaml_physical_equal in Hsame.
  eapply runtime_same_represents_equal.
  - apply state_root_represents_forgets_allocation.
    exact (@object_represents Tree state empty changed).
  - apply state_root_represents_forgets_allocation.
    exact (@object_represents Tree state empty original).
  - exact Hsame.
Qed.

(** This is the exact local adequacy obligation for the extraction directive
    [Extract Inlined Constant ...native_same => "(==)"].  At a particular
    dynamic call, the source callback result must be the OCaml physical test
    on the two values passed to that call.  It is intentionally a relation on
    [tree_object]s, not a claim that a pure source tree has a unique address. *)
Definition native_same_call_adequate {Tree : Type} (state : heap_state Tree)
    (empty : Tree) (same : Tree -> Tree -> bool)
    (changed original : tree_object state empty) : Prop :=
  same (@object_tree Tree state empty changed)
    (@object_tree Tree state empty original) =
    ocaml_physical_equal changed original.

Lemma native_same_call_adequate_sound:
  forall (Tree : Type) (state : heap_state Tree) (empty : Tree)
      (same : Tree -> Tree -> bool)
      (changed original : tree_object state empty),
    native_same_call_adequate state empty same changed original ->
    same (@object_tree Tree state empty changed)
      (@object_tree Tree state empty original) = true ->
    @object_tree Tree state empty changed = @object_tree Tree state empty original.
Proof.
  intros Tree state empty same changed original Hadequate Hsame.
  apply ocaml_physical_equal_sound.
  unfold native_same_call_adequate in Hadequate.
  now rewrite <- Hadequate.
Qed.

(** A whole-worker target simulation supplies objects for every successful
    source-level [native_same] call.  This formulation permits different
    locations for extensionally (or even structurally) equal source trees,
    while requiring the locations actually compared by a successful [(==)]
    to agree.  It is the remaining external OCaml heap/compiler theorem. *)
Definition native_same_refines_ocaml_heap {Tree : Type}
    (state : heap_state Tree) (empty : Tree) (same : Tree -> Tree -> bool) : Prop :=
  forall changed original,
    same changed original = true ->
    exists changed_object original_object : tree_object state empty,
      @object_tree Tree state empty changed_object = changed /\
      @object_tree Tree state empty original_object = original /\
      native_same_call_adequate state empty same changed_object original_object.

Lemma native_same_refines_ocaml_heap_sound:
  forall (Tree : Type) (state : heap_state Tree) (empty : Tree)
      (same : Tree -> Tree -> bool),
    native_same_refines_ocaml_heap state empty same ->
    forall changed original,
      same changed original = true -> changed = original.
Proof.
  intros Tree state empty same Hrefines changed original Hsame.
  destruct (Hrefines changed original Hsame)
    as [changed_object [original_object
      [Hchanged [Horiginal Hadequate]]]].
  pose proof (native_same_call_adequate_sound Tree state empty same
    changed_object original_object Hadequate) as Hobjects.
  rewrite Hchanged, Horiginal in Hobjects.
  apply Hobjects. exact Hsame.
Qed.

Theorem patricia_ocaml_heap_same_sound:
  forall (A : Type) (state : heap_state (Patricia.t A))
      (same : Patricia.t A -> Patricia.t A -> bool),
    native_same_refines_ocaml_heap state Patricia.Empty same ->
    PatriciaUnionProof.native_same_sound same.
Proof.
  intros A state same Hrefines changed original Hsame.
  pose proof (native_same_refines_ocaml_heap_sound (Patricia.t A) state
    Patricia.Empty same Hrefines changed original Hsame) as Htrees.
  subst original. apply PatriciaProof.equiv_refl.
Qed.

Theorem string_patricia_ocaml_heap_same_sound:
  forall (A : Type) (state : heap_state (StringPatricia.t A))
      (same : StringPatricia.t A -> StringPatricia.t A -> bool),
    native_same_refines_ocaml_heap state StringPatricia.Empty same ->
    StringPatriciaUnionProof.native_same_sound same.
Proof.
  intros A state same Hrefines changed original Hsame.
  pose proof (native_same_refines_ocaml_heap_sound (StringPatricia.t A) state
    StringPatricia.Empty same Hrefines changed original Hsame) as Htrees.
  subst original. apply StringPatriciaProof.equiv_refl.
Qed.
