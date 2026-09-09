(** Experimental source counterpart of the optimized integer biased union.
    This companion module deliberately keeps worker iteration out of the
    established [Patricia.v]/[PatriciaProof.v] closure. *)

From Stdlib Require Import Bool Lia NArith PArith Wf_nat.
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

(** A source-level change signal for the sharing optimization.  [Empty] means
    that the left-biased union has exactly the original left tree as its
    result; every nonempty tree is the rebuilt result otherwise.  A changed
    biased union cannot be empty, so this reuses the nullary tree constructor
    as an allocation-free sentinel after extraction.  Unlike OCaml physical
    equality, the signal is ordinary data in the source semantics and can
    therefore receive a refinement proof. *)
Fixpoint union_left_specialized_changed {A : Type} (a : t A) {struct a}
    : t A -> t A :=
  match a with
  | Empty => fun b =>
      b
  | Leaf ka va => fun b =>
      match b with
      | Empty => Empty
      | Leaf kb _ => if Pos.eqb ka kb then Empty else set ka va b
      | Branch _ _ _ _ => set ka va b
      end
  | Branch pa ma la ra =>
      fix union_right_tree (b : t A) {struct b} : t A :=
        match b with
        | Empty => Empty
        | Leaf kb vb =>
            match get kb a with Some _ => Empty | None => set kb vb a end
        | Branch pb mb lb rb =>
            if (N.eqb ma mb && N.eqb pa pb)%bool then
              match union_left_specialized_changed la lb,
                    union_left_specialized_changed ra rb with
              | Empty, Empty => Empty
              | left', Empty => branch pa ma left' ra
              | Empty, right' => branch pa ma la right'
              | left', right' => branch pa ma left' right'
              end
            else if mask_above ma mb then
              match representative b with
              | Some kb =>
                  if matches_prefix kb pa ma then
                    if zero_bit kb ma then
                      match union_left_specialized_changed la b with
                      | Empty => Empty
                      | left' => branch pa ma left' ra
                      end
                    else
                      match union_left_specialized_changed ra b with
                      | Empty => Empty
                      | right' => branch pa ma la right'
                      end
                  else join a b
              | None => Empty
              end
            else if mask_above mb ma then
              match representative a with
              | Some ka =>
                  if matches_prefix ka pb mb then
                    if zero_bit ka mb then
                      match union_right_tree lb with
                      | Empty => branch pb mb a rb
                      | left' => branch pb mb left' rb
                      end
                    else
                      match union_right_tree rb with
                      | Empty => branch pb mb lb a
                      | right' => branch pb mb lb right'
                      end
                  else join a b
              | None => b
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

(** Source model of the native [==] child-reuse decision.  It is deliberately
    parameterized by a Boolean test: the proof only needs a test reporting
    [true] to imply observational equality.  Native refinement later
    instantiates it with physical identity. *)
Definition native_reuse_child {A : Type} (same : t A -> t A -> bool)
    (original changed : t A) : t A :=
  if same changed original then original else changed.

Definition native_reuse_same_branch {A : Type} (same : t A -> t A -> bool)
    (prefix mask : N) (left_original right_original left_changed right_changed : t A)
    : t A :=
  Branch prefix mask
    (native_reuse_child same left_original left_changed)
    (native_reuse_child same right_original right_changed).

Definition native_reuse_left_branch {A : Type} (same : t A -> t A -> bool)
    (prefix mask : N) (left_original right_original left_changed : t A) : t A :=
  Branch prefix mask (native_reuse_child same left_original left_changed)
    right_original.

Definition native_reuse_right_branch {A : Type} (same : t A -> t A -> bool)
    (prefix mask : N) (left_original right_original right_changed : t A) : t A :=
  Branch prefix mask left_original
    (native_reuse_child same right_original right_changed).

(** Exact root-reuse forms used by the extracted worker.  The earlier helpers
    model child substitution; these additionally avoid allocating the parent
    when all of its changed children are physically reusable. *)
Definition native_reuse_same_branch_root {A : Type} (same : t A -> t A -> bool)
    (original : t A) (prefix mask : N)
    (left_original right_original left_changed right_changed : t A) : t A :=
  if (same left_changed left_original && same right_changed right_original)%bool
  then original
  else Branch prefix mask
    (native_reuse_child same left_original left_changed)
    (native_reuse_child same right_original right_changed).

Definition native_reuse_left_branch_root {A : Type} (same : t A -> t A -> bool)
    (original : t A) (prefix mask : N)
    (left_original right_original left_changed : t A) : t A :=
  if same left_changed left_original then original
  else Branch prefix mask (native_reuse_child same left_original left_changed)
    right_original.

Definition native_reuse_right_branch_root {A : Type} (same : t A -> t A -> bool)
    (original : t A) (prefix mask : N)
    (left_original right_original right_changed : t A) : t A :=
  if same right_changed right_original then original
  else Branch prefix mask left_original
    (native_reuse_child same right_original right_changed).

(** The handwritten OCaml union, expressed in Rocq with its sole native
    operation abstracted as [same].  Unlike the changed-result worker, this
    retains the original branch whenever both recursive results are physically
    reusable.  Extraction maps [native_same] to [(==)]; proofs use the worker
    polymorphically under [native_same_sound]. *)
Fixpoint union_left_native {A : Type} (same : t A -> t A -> bool) (a : t A)
    {struct a} : t A -> t A :=
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
              native_reuse_same_branch_root same a pa ma la ra
                (union_left_native same la lb)
                (union_left_native same ra rb)
            else if mask_above ma mb then
              match representative b with
              | Some kb =>
                  if matches_prefix kb pa ma then
                    if zero_bit kb ma then
                      native_reuse_left_branch_root same a pa ma la ra
                        (union_left_native same la b)
                    else native_reuse_right_branch_root same a pa ma la ra
                        (union_left_native same ra b)
                  else join a b
              | None => a
              end
            else if mask_above mb ma then
              match representative a with
              | Some ka =>
                  if matches_prefix ka pb mb then
                    if zero_bit ka mb then
                      native_reuse_left_branch_root same b pb mb lb rb
                        (union_right_tree lb)
                    else native_reuse_right_branch_root same b pb mb lb rb
                        (union_right_tree rb)
                  else join a b
              | None => b
              end
            else join a b
        end
  end.

(** Pure source placeholder for the extraction-only physical comparison. *)
Definition native_same {A : Type} (_ _ : t A) : bool := false.

Definition union_left_native_default {A : Type} : t A -> t A -> t A :=
  union_left_native (@native_same A).

(** The handwritten right-biased realizer is exactly the left-biased native
    worker with its arguments swapped.  Keep that target-level shape visible
    in the source model so its functional refinement is not merely inferred
    from the uninstrumented OCaml directive. *)
Definition union_right_native {A : Type} (same : t A -> t A -> bool)
    (a b : t A) : t A :=
  union_left_native same b a.

Definition union_right_native_default {A : Type} : t A -> t A -> t A :=
  union_right_native (@native_same A).

(** Two-argument unfolding rule for the native-shaped worker.  As with the
    specialized worker's equation, this hides whether the recursive call is
    made by the outer or locally nested structural fixpoint. *)
Lemma union_left_native_equation:
  forall (A : Type) (same : t A -> t A -> bool) (a b : t A),
    union_left_native same a b =
    match a, b with
    | Empty, tree => tree
    | tree, Empty => tree
    | Leaf ka va, Leaf kb _ => if Pos.eqb ka kb then a else set ka va b
    | Leaf ka va, tree => set ka va tree
    | tree, Leaf kb vb =>
        match get kb tree with Some _ => tree | None => set kb vb tree end
    | Branch pa ma la ra, Branch pb mb lb rb =>
        if (N.eqb ma mb && N.eqb pa pb)%bool then
          native_reuse_same_branch_root same a pa ma la ra
            (union_left_native same la lb)
            (union_left_native same ra rb)
        else if mask_above ma mb then
          match representative b with
          | Some kb =>
              if matches_prefix kb pa ma then
                if zero_bit kb ma then
                  native_reuse_left_branch_root same a pa ma la ra
                    (union_left_native same la b)
                else native_reuse_right_branch_root same a pa ma la ra
                  (union_left_native same ra b)
              else join a b
          | None => a
          end
        else if mask_above mb ma then
          match representative a with
          | Some ka =>
              if matches_prefix ka pb mb then
                if zero_bit ka mb then
                  native_reuse_left_branch_root same b pb mb lb rb
                    (union_left_native same a lb)
                else native_reuse_right_branch_root same b pb mb lb rb
                  (union_left_native same a rb)
              else join a b
          | None => b
          end
        else join a b
    end.
Proof. intros A same a b. destruct a; destruct b; reflexivity. Qed.

(** Closure-free variant of [union_left_native].  Its single decreasing fuel
    argument avoids extracting the branch-local recursive closure introduced
    by the nested structural definition above.  A sufficient bound is supplied
    by [size] at the public experimental entry point. *)
Fixpoint union_left_native_fuel {A : Type} (same : t A -> t A -> bool)
    (fuel : nat) (a b : t A) : t A :=
  match fuel with
  | O => union_left_specialized a b
  | S fuel' =>
      match a, b with
      | Empty, tree => tree
      | tree, Empty => tree
      | Leaf ka va, Leaf kb _ => if Pos.eqb ka kb then a else set ka va b
      | Leaf ka va, tree => set ka va tree
      | tree, Leaf kb vb =>
          match get kb tree with Some _ => tree | None => set kb vb tree end
      | Branch pa ma la ra, Branch pb mb lb rb =>
          if (N.eqb ma mb && N.eqb pa pb)%bool then
            native_reuse_same_branch_root same a pa ma la ra
              (union_left_native_fuel same fuel' la lb)
              (union_left_native_fuel same fuel' ra rb)
          else if mask_above ma mb then
            match representative b with
            | Some kb =>
                if matches_prefix kb pa ma then
                  if zero_bit kb ma then
                    native_reuse_left_branch_root same a pa ma la ra
                      (union_left_native_fuel same fuel' la b)
                  else native_reuse_right_branch_root same a pa ma la ra
                    (union_left_native_fuel same fuel' ra b)
                else join a b
            | None => a
            end
          else if mask_above mb ma then
            match representative a with
            | Some ka =>
                if matches_prefix ka pb mb then
                  if zero_bit ka mb then
                    native_reuse_left_branch_root same b pb mb lb rb
                      (union_left_native_fuel same fuel' a lb)
                  else native_reuse_right_branch_root same b pb mb lb rb
                    (union_left_native_fuel same fuel' a rb)
                else join a b
            | None => b
            end
          else join a b
      end
  end.

Definition union_left_native_fuel_default {A : Type} (a b : t A) : t A :=
  union_left_native_fuel (@native_same A) (S (size a + size b)) a b.

(** Code-generation experiment: specialize [same] and spell the root tests
    directly in the recursive worker, avoiding higher-order calls and the
    reusable helper functions. *)
Fixpoint union_left_native_fuel_inline {A : Type}
    (fuel : nat) (a b : t A) : t A :=
  match fuel with
  | O => union_left_specialized a b
  | S fuel' =>
      match a, b with
      | Empty, tree => tree
      | tree, Empty => tree
      | Leaf ka va, Leaf kb _ => if Pos.eqb ka kb then a else set ka va b
      | Leaf ka va, tree => set ka va tree
      | tree, Leaf kb vb =>
          match get kb tree with Some _ => tree | None => set kb vb tree end
      | Branch pa ma la ra, Branch pb mb lb rb =>
          if (N.eqb ma mb && N.eqb pa pb)%bool then
            let left' := union_left_native_fuel_inline fuel' la lb in
            let right' := union_left_native_fuel_inline fuel' ra rb in
            if (native_same left' la && native_same right' ra)%bool then a
            else Branch pa ma
              (if native_same left' la then la else left')
              (if native_same right' ra then ra else right')
          else if mask_above ma mb then
            match representative b with
            | Some kb =>
                if matches_prefix kb pa ma then
                  if zero_bit kb ma then
                    let left' := union_left_native_fuel_inline fuel' la b in
                    if native_same left' la then a
                    else Branch pa ma (if native_same left' la then la else left') ra
                  else
                    let right' := union_left_native_fuel_inline fuel' ra b in
                    if native_same right' ra then a
                    else Branch pa ma la (if native_same right' ra then ra else right')
                else join a b
            | None => a
            end
          else if mask_above mb ma then
            match representative a with
            | Some ka =>
                if matches_prefix ka pb mb then
                  if zero_bit ka mb then
                    let left' := union_left_native_fuel_inline fuel' a lb in
                    if native_same left' lb then b
                    else Branch pb mb (if native_same left' lb then lb else left') rb
                  else
                    let right' := union_left_native_fuel_inline fuel' a rb in
                    if native_same right' rb then b
                    else Branch pb mb lb (if native_same right' rb then rb else right')
                else join a b
            | None => b
            end
          else join a b
      end
  end.

Definition union_left_native_fuel_inline_default {A : Type} (a b : t A) : t A :=
  union_left_native_fuel_inline (S (size a + size b)) a b.

(** The six recursive branch/branch pairs all decrease the combined tree
    size.  Keeping this elementary fact beside the worker lets its termination
    argument live entirely in [Prop], where extraction can erase it. *)
Lemma union_left_native_acc_branch_calls_smaller:
  forall (A : Type) pa ma (la ra : t A) pb mb (lb rb : t A),
    size la + size lb < size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size ra + size rb < size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size la + size (Branch pb mb lb rb) <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size ra + size (Branch pb mb lb rb) <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size (Branch pa ma la ra) + size lb <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb) /\
    size (Branch pa ma la ra) + size rb <
      size (Branch pa ma la ra) + size (Branch pb mb lb rb).
Proof. intros. cbn [size]. lia. Qed.

(** Rewriting a child-measure argument through an erased tree equality. *)
Lemma union_left_native_acc_smaller_right:
  forall (A : Type) (x : nat) (current original : t A) total,
    original = current -> x + size current < total -> x + size original < total.
Proof. intros A x current original total H; subst original; exact (fun H' => H'). Qed.

Lemma union_left_native_acc_smaller_left:
  forall (A : Type) (current original : t A) (x total : nat),
    original = current -> size current + x < total -> size original + x < total.
Proof. intros A current original x total H; subst original; exact (fun H' => H'). Qed.

(** Closure-free native-shaped worker.  Its proof-only accessibility witness
    governs recursion, while explicit original-root aliases preserve physical
    root identity through the dependent tree match after extraction. *)
Fixpoint union_left_native_acc {A : Type}
    (same : t A -> t A -> bool) (original_a original_b a b : t A)
    (original_a_is_a : original_a = a) (original_b_is_b : original_b = b)
    (termination : Acc lt (size a + size b))
    {struct termination} : t A :=
  match a as a0, b as b0
      return original_a = a0 -> original_b = b0 ->
        Acc lt (size a0 + size b0) -> t A with
  | Empty, _ => fun _ _ _ => original_b
  | _, Empty => fun _ _ _ => original_a
  | Leaf ka va, Leaf kb _ => fun _ _ _ =>
      if Pos.eqb ka kb then original_a else set ka va original_b
  | Leaf ka va, Branch _ _ _ _ => fun _ _ _ => set ka va original_b
  | Branch _ _ _ _, Leaf kb vb => fun _ _ _ =>
      match get kb original_a with
      | Some _ => original_a
      | None => set kb vb original_a
      end
  | Branch pa ma la ra, Branch pb mb lb rb => fun H_a H_b termination0 =>
      match termination0 with
      | Acc_intro _ smaller =>
          if (N.eqb ma mb && N.eqb pa pb)%bool then
            let decreases := union_left_native_acc_branch_calls_smaller
              A pa ma la ra pb mb lb rb in
            native_reuse_same_branch_root same original_a pa ma la ra
              (union_left_native_acc same la lb la lb eq_refl eq_refl
                (smaller _ (proj1 decreases)))
              (union_left_native_acc same ra rb ra rb eq_refl eq_refl
                (smaller _ (proj1 (proj2 decreases))))
          else if mask_above ma mb then
            match representative original_b with
            | Some kb =>
                if matches_prefix kb pa ma then
                  let decreases := union_left_native_acc_branch_calls_smaller
                    A pa ma la ra pb mb lb rb in
                  if zero_bit kb ma then
                    native_reuse_left_branch_root same original_a pa ma la ra
                      (union_left_native_acc same la original_b la original_b
                        eq_refl eq_refl
                        (smaller _ (union_left_native_acc_smaller_right A
                          (size la) (Branch pb mb lb rb) original_b _ H_b
                          (proj1 (proj2 (proj2 decreases))))))
                  else native_reuse_right_branch_root same original_a pa ma la ra
                    (union_left_native_acc same ra original_b ra original_b
                      eq_refl eq_refl
                      (smaller _ (union_left_native_acc_smaller_right A
                        (size ra) (Branch pb mb lb rb) original_b _ H_b
                        (proj1 (proj2 (proj2 (proj2 decreases)))))))
                else join original_a original_b
            | None => original_a
            end
          else if mask_above mb ma then
            match representative original_a with
            | Some ka =>
                if matches_prefix ka pb mb then
                  let decreases := union_left_native_acc_branch_calls_smaller
                    A pa ma la ra pb mb lb rb in
                  if zero_bit ka mb then
                    native_reuse_left_branch_root same original_b pb mb lb rb
                      (union_left_native_acc same original_a lb original_a lb
                        eq_refl eq_refl
                        (smaller _ (union_left_native_acc_smaller_left A
                          (Branch pa ma la ra) original_a (size lb) _ H_a
                          (proj1 (proj2 (proj2 (proj2 (proj2 decreases))))))))
                  else native_reuse_right_branch_root same original_b pb mb lb rb
                    (union_left_native_acc same original_a rb original_a rb
                      eq_refl eq_refl
                      (smaller _ (union_left_native_acc_smaller_left A
                        (Branch pa ma la ra) original_a (size rb) _ H_a
                        (proj2 (proj2 (proj2 (proj2 (proj2 decreases))))))))
                else join original_a original_b
            | None => original_b
            end
          else join original_a original_b
      end
  end original_a_is_a original_b_is_b termination.

Definition union_left_native_acc_default {A : Type} (a b : t A) : t A :=
  union_left_native_acc (@native_same A) a b a b eq_refl eq_refl
    (lt_wf (size a + size b)).

Definition union_right_native_acc_default {A : Type} (a b : t A) : t A :=
  union_left_native_acc_default b a.

(** One-step equation for changed-result refinement proofs. *)
Lemma union_left_specialized_changed_equation:
  forall (A : Type) (a b : t A),
    union_left_specialized_changed a b =
    match a, b with
    | Empty, tree => tree
    | _, Empty => Empty
    | Leaf ka va, Leaf kb _ =>
        if Pos.eqb ka kb then Empty else set ka va b
    | Leaf ka va, tree => set ka va tree
    | tree, Leaf kb vb =>
        match get kb tree with Some _ => Empty | None => set kb vb tree end
    | Branch pa ma la ra, Branch pb mb lb rb =>
        if (N.eqb ma mb && N.eqb pa pb)%bool then
          match union_left_specialized_changed la lb,
                union_left_specialized_changed ra rb with
          | Empty, Empty => Empty
          | left', Empty => branch pa ma left' ra
          | Empty, right' => branch pa ma la right'
          | left', right' => branch pa ma left' right'
          end
        else if mask_above ma mb then
          match representative b with
          | Some kb =>
              if matches_prefix kb pa ma then
                if zero_bit kb ma then
                  match union_left_specialized_changed la b with
                  | Empty => Empty
                  | left' => branch pa ma left' ra
                  end
                else
                  match union_left_specialized_changed ra b with
                  | Empty => Empty
                  | right' => branch pa ma la right'
                  end
              else join a b
          | None => Empty
          end
        else if mask_above mb ma then
          match representative a with
          | Some ka =>
              if matches_prefix ka pb mb then
                if zero_bit ka mb then
                  match union_left_specialized_changed a lb with
                  | Empty => branch pb mb a rb
                  | left' => branch pb mb left' rb
                  end
                else
                  match union_left_specialized_changed a rb with
                  | Empty => branch pb mb lb a
                  | right' => branch pb mb lb right'
                  end
              else join a b
          | None => b
          end
        else join a b
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
    : t A :=
  union_left_specialized_changed b a.

Definition union_right_specialized_changed_result {A : Type} (a b : t A) : t A :=
  union_left_specialized_changed_result b a.

(** Closure-free changed worker.  Recursion is directly on [fuel], so the
    extracted code has one recursive function rather than a branch-local
    closure.  The public experiment supplies the structural bound below;
    its equality to the nested worker is proved in the companion closure
    before this worker can replace the current exported implementation. *)
Fixpoint union_left_specialized_changed_fuel {A : Type}
    (fuel : nat) (a b : t A) : t A :=
  match fuel with
  | O => Empty
  | S fuel' =>
      match a, b with
      | Empty, tree => tree
      | _, Empty => Empty
      | Leaf ka va, Leaf kb _ =>
          if Pos.eqb ka kb then Empty else set ka va b
      | Leaf ka va, tree => set ka va tree
      | tree, Leaf kb vb =>
          match get kb tree with Some _ => Empty | None => set kb vb tree end
      | Branch pa ma la ra, Branch pb mb lb rb =>
          if (N.eqb ma mb && N.eqb pa pb)%bool then
            match union_left_specialized_changed_fuel fuel' la lb,
                  union_left_specialized_changed_fuel fuel' ra rb with
            | Empty, Empty => Empty
            | left', Empty => branch pa ma left' ra
            | Empty, right' => branch pa ma la right'
            | left', right' => branch pa ma left' right'
            end
          else if mask_above ma mb then
            match representative b with
            | Some kb =>
                if matches_prefix kb pa ma then
                  if zero_bit kb ma then
                    match union_left_specialized_changed_fuel fuel' la b with
                    | Empty => Empty
                    | left' => branch pa ma left' ra
                    end
                  else
                    match union_left_specialized_changed_fuel fuel' ra b with
                    | Empty => Empty
                    | right' => branch pa ma la right'
                    end
                else join a b
            | None => Empty
            end
          else if mask_above mb ma then
            match representative a with
            | Some ka =>
                if matches_prefix ka pb mb then
                  if zero_bit ka mb then
                    match union_left_specialized_changed_fuel fuel' a lb with
                    | Empty => branch pb mb a rb
                    | left' => branch pb mb left' rb
                    end
                  else
                    match union_left_specialized_changed_fuel fuel' a rb with
                    | Empty => branch pb mb lb a
                    | right' => branch pb mb lb right'
                    end
                else join a b
            | None => b
            end
          else join a b
      end
  end.

Definition union_left_specialized_changed_fuel_result {A : Type} (a b : t A)
    : t A :=
  reuse_changed a
    (union_left_specialized_changed_fuel (S (size a + size b)) a b).
