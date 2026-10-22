From Coq Require Import List Arith ZArith Lia Permutation.
Import ListNotations.
Open Scope Z_scope.

(* Mathematical finite-heap semantics for the differential counterexample.
   This does not establish a refinement theorem for the C++ implementation. *)
Definition Heap := list (Z * Z)%type.
Definition domain (h : Heap) := map fst h.
Definition valid (h : Heap) := NoDup (domain h) /\ ~ In 0 (domain h).
Definition disjoint (h k : Heap) :=
  forall a, In a (domain h) -> ~ In a (domain k).
Definition Predicate := Heap -> Prop.
Definition pto (a : Z) (v : Z) : Predicate :=
  fun h => Permutation h [(a, v)] /\ a <> 0.
Definition wand (P Q : Predicate) : Predicate :=
  fun h => forall k, valid k -> disjoint h k -> P k -> Q (h ++ k).

Fixpoint ceiling (h : Heap) : Z :=
  match h with [] => 0 | (a, _) :: tail => Z.max a (ceiling tail) end.

Lemma domain_below_ceiling h a : In a (domain h) -> a <= ceiling h.
Proof.
  induction h as [|[b v] tail IH]; unfold domain in *; simpl in *.
  - contradiction.
  - intros [H | H].
    + subst a. apply Z.le_max_l.
    + eapply Z.le_trans; [apply IH; exact H | apply Z.le_max_r].
Qed.

Lemma ceiling_nonnegative h : 0 <= ceiling h.
Proof.
  induction h as [|[a v] tail IH]; simpl; [lia |].
  eapply Z.le_trans; [exact IH | apply Z.le_max_r].
Qed.

Definition fresh (h : Heap) : Heap :=
  [(ceiling h + 1, 0); (ceiling h + 2, 0)].

Lemma fresh_valid h : valid (fresh h).
Proof.
  pose proof (ceiling_nonnegative h).
  unfold valid, domain, fresh. simpl. split.
  - constructor.
    + simpl. intuition lia.
    + constructor; [simpl; tauto | constructor].
  - intuition lia.
Qed.

Lemma fresh_disjoint h : disjoint h (fresh h).
Proof.
  intros a Hin Hfresh.
  pose proof (domain_below_ceiling h a Hin).
  unfold domain, fresh in Hfresh. simpl in Hfresh. intuition lia.
Qed.

Theorem false_wand_is_true (P : Predicate) h :
  wand (fun _ => False) P h.
Proof. unfold wand. intros k Hvalid Hdisjoint Hfalse. contradiction. Qed.

Theorem true_wand_pto_impossible a v h :
  ~ wand (fun _ => True) (pto a v) h.
Proof.
  intro H.
  specialize (H (fresh h) (fresh_valid h) (fresh_disjoint h) I).
  destruct H as [Hperm _].
  apply Permutation_length in Hperm.
  rewrite app_length in Hperm.
  unfold fresh in Hperm. simpl in Hperm. lia.
Qed.

Theorem nested_false_wand_pto_impossible a v h :
  ~ wand (wand (fun _ => False) (pto a v)) (pto a v) h.
Proof.
  intro H. apply (true_wand_pto_impossible a v h).
  intros k Hvalid Hdisjoint _.
  apply H; [exact Hvalid | exact Hdisjoint | apply false_wand_is_true].
Qed.

Print Assumptions false_wand_is_true.
Print Assumptions true_wand_pto_impossible.
Print Assumptions nested_false_wand_pto_impossible.

Definition emp : Predicate := fun h => h = [].
Definition sep (P Q : Predicate) : Predicate :=
  fun h => exists left right,
    valid left /\ valid right /\ disjoint left right /\
    Permutation h (left ++ right) /\ P left /\ Q right.

Lemma valid_empty : valid [].
Proof. split; [constructor | simpl; tauto]. Qed.

Lemma disjoint_empty_right h : disjoint h [].
Proof. unfold disjoint, domain. simpl. tauto. Qed.

Lemma emp_sep_left P h : valid h -> P h -> sep emp P h.
Proof.
  intros Hvalid HP. exists [], h.
  split; [apply valid_empty |].
  split; [exact Hvalid |].
  split; [unfold disjoint, domain; simpl; tauto |].
  split; [simpl; apply Permutation_refl |].
  split; [reflexivity | exact HP].
Qed.

Theorem not_pto_wand_emp_impossible a v h :
  ~ wand (fun k => ~ pto a v k) emp h.
Proof.
  intro H.
  assert (Hnot : ~ pto a v (fresh h)).
  { intros [Hperm _]. apply Permutation_length in Hperm.
    unfold fresh in Hperm. simpl in Hperm. lia. }
  specialize (H (fresh h) (fresh_valid h) (fresh_disjoint h) Hnot).
  unfold emp in H. apply app_eq_nil in H. destruct H as [_ Hbad].
  unfold fresh in Hbad. discriminate.
Qed.

Theorem nonempty_or_wand_pto_impossible (P : Predicate) a v h :
  ~ wand (fun k => ~ emp k \/ P k) (pto a v) h.
Proof.
  intro H.
  assert (Hnonempty : ~ emp (fresh h)).
  { unfold emp, fresh. discriminate. }
  specialize (H (fresh h) (fresh_valid h) (fresh_disjoint h) (or_introl Hnonempty)).
  destruct H as [Hperm _].
  apply Permutation_length in Hperm. rewrite app_length in Hperm.
  unfold fresh in Hperm. simpl in Hperm. lia.
Qed.

(* The original case-236 SMT formula, manually specialized to nil = 0.
   Addresses and data both range over Z, exactly as in the native heap query.
   No claim here verifies the SMT parser or the manual translation. *)
Definition case236 (x : Z) : Predicate :=
  sep emp
    (wand (fun h => (False /\ emp h) \/
             wand (fun _ => x <> 0) (pto x 0) h)
          (fun _ => False)).

Theorem case236_iff_non_nil x h :
  valid h -> (case236 x h <-> x <> 0).
Proof.
  intro Hvalid. split.
  - intros Hcase Hzero. subst x.
    destruct Hcase as [left [right [HL [HR [HD [HP [HE HW]]]]]]].
    specialize (HW [] valid_empty (disjoint_empty_right right)).
    apply HW. right.
    intros k HK HDK Hneq. exfalso. apply Hneq. reflexivity.
  - intro Hnonzero. apply emp_sep_left; [exact Hvalid |].
    intros k HK HDK [Hfalse | Hinner].
    + destruct Hfalse as [Hfalse _]. contradiction.
    + apply (true_wand_pto_impossible x 0 k).
      intros extension HV HE _.
      apply Hinner; [exact HV | exact HE | exact Hnonzero].
Qed.

Theorem native_case236_empty_model : case236 1 [].
Proof. apply (proj2 (case236_iff_non_nil 1 [] valid_empty)). lia. Qed.

Print Assumptions not_pto_wand_emp_impossible.
Print Assumptions nonempty_or_wand_pto_impossible.
Print Assumptions case236_iff_non_nil.
Print Assumptions native_case236_empty_model.
