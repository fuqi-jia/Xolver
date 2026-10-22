From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(* Mathematical rules used by the independent C++ certificate checkers.
   These theorems do not assert a refinement proof of the C++ implementation. *)
Definition WeightedPremise := (Z * Z * Z)%type.
Definition weight (p : WeightedPremise) := fst (fst p).
Definition lhs (p : WeightedPremise) := snd (fst p).
Definition rhs (p : WeightedPremise) := snd p.
Fixpoint left_sum (ps : list WeightedPremise) : Z :=
  match ps with [] => 0 | p :: rest => weight p * lhs p + left_sum rest end.
Fixpoint right_sum (ps : list WeightedPremise) : Z :=
  match ps with [] => 0 | p :: rest => weight p * rhs p + right_sum rest end.

Theorem nonnegative_linear_combination ps :
  Forall (fun p => 0 <= weight p /\ lhs p <= rhs p) ps ->
  left_sum ps <= right_sum ps.
Proof.
  intro H. induction H; simpl; [lia | destruct H; nia].
Qed.

Theorem linear_contradiction ps :
  Forall (fun p => 0 <= weight p /\ lhs p <= rhs p) ps ->
  left_sum ps = 0 -> right_sum ps < 0 -> False.
Proof.
  intros H Hz Hneg.
  pose proof (nonnegative_linear_combination ps H). lia.
Qed.

Theorem integer_rounding g x b :
  0 < g -> g * x <= b -> x <= b / g.
Proof.
  intros Hg Hbound. apply Z.div_le_lower_bound; nia.
Qed.

Theorem divisibility_contradiction g x b :
  ~ (g | b) -> g * x = b -> False.
Proof.
  intros Hnot Heq. apply Hnot. exists x. nia.
Qed.

(* A path certificate refers to input equality premises by list index and
   orientation. This executable checker is independent of union-find search. *)
Definition Edge := (nat * nat)%type.
Definition Step := (nat * bool)%type.
Fixpoint check_path (premises : list Edge) (current target : nat)
                    (steps : list Step) : bool :=
  match steps with
  | [] => Nat.eqb current target
  | (index, reverse) :: rest =>
      match nth_error premises index with
      | None => false
      | Some (a, b) =>
          let source := if reverse then b else a in
          let destination := if reverse then a else b in
          Nat.eqb current source && check_path premises destination target rest
      end
  end.

Theorem path_checker_sound premises (valuation : nat -> nat) :
  Forall (fun p => valuation (fst p) = valuation (snd p)) premises ->
  forall steps current target,
    check_path premises current target steps = true ->
    valuation current = valuation target.
Proof.
  intros Hpremises steps.
  induction steps as [| [index reverse] rest IH]; intros current target Hcheck.
  - simpl in Hcheck. apply Nat.eqb_eq in Hcheck. now subst.
  - simpl in Hcheck.
    unfold Edge in Hcheck.
    destruct (nth_error premises index) as [[a b]|] eqn:Hedge;
      try rewrite Hedge in Hcheck; try discriminate.
    assert (Heq : valuation a = valuation b).
    { rewrite Forall_forall in Hpremises.
      apply (Hpremises (a,b)). now apply nth_error_In in Hedge. }
    destruct reverse; simpl in Hcheck;
      apply andb_true_iff in Hcheck; destruct Hcheck as [Hstart Hrest];
      apply Nat.eqb_eq in Hstart; subst current.
    + specialize (IH a target Hrest). congruence.
    + specialize (IH b target Hrest). congruence.
Qed.

Theorem location_disequality_conflict premises (valuation : nat -> nat) steps a b :
  Forall (fun p => valuation (fst p) = valuation (snd p)) premises ->
  check_path premises a b steps = true ->
  valuation a <> valuation b -> False.
Proof.
  intros H Hpath Hneq. apply Hneq.
  exact (path_checker_sound premises valuation H steps a b Hpath).
Qed.

Theorem nonnull_allocation_conflict premises (valuation : nat -> nat) steps address :
  Forall (fun p => valuation (fst p) = valuation (snd p)) premises ->
  valuation 0%nat = 0%nat ->
  check_path premises address 0%nat steps = true ->
  valuation address <> 0%nat -> False.
Proof.
  intros H Hnil Hpath Hnonnull. apply Hnonnull.
  pose proof (path_checker_sound premises valuation H steps address 0%nat Hpath).
  congruence.
Qed.

Print Assumptions linear_contradiction.
Print Assumptions integer_rounding.
Print Assumptions divisibility_contradiction.
Print Assumptions path_checker_sound.
Print Assumptions location_disequality_conflict.
Print Assumptions nonnull_allocation_conflict.
