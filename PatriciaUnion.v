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
