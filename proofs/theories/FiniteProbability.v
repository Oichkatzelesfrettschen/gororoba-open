(** Finite weighted laws. Dependence between observables is unrestricted. *)
From Stdlib Require Import Reals List Lra Psatz.
Import ListNotations.
Open Scope R_scope.

Definition weighted_expectation {A : Type} (law : list (A * R))
    (observable : A -> R) : R :=
  fold_right (fun point total => snd point * observable (fst point) + total) 0 law.
Definition nonnegative_law {A : Type} (law : list (A * R)) : Prop :=
  Forall (fun point => 0 <= snd point) law.
Definition normalized_law {A : Type} (law : list (A * R)) : Prop :=
  weighted_expectation law (fun _ => 1) = 1.
Definition indicator {A : Type} (event : A -> bool) (point : A) : R :=
  if event point then 1 else 0.
Definition event_probability {A : Type} (law : list (A * R))
    (event : A -> bool) : R := weighted_expectation law (indicator event).

Lemma weighted_expectation_ext {A} (law : list (A * R)) f g :
  (forall point, f point = g point) ->
  weighted_expectation law f = weighted_expectation law g.
Proof. intros Heq; induction law as [|[point weight] rest IH]; simpl; [reflexivity|].
  rewrite Heq, IH; reflexivity. Qed.
Lemma weighted_expectation_add {A} (law : list (A * R)) f g :
  weighted_expectation law (fun point => f point + g point) =
  weighted_expectation law f + weighted_expectation law g.
Proof. induction law as [|[point weight] rest IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma weighted_expectation_scale {A} (law : list (A * R)) scalar f :
  weighted_expectation law (fun point => scalar * f point) =
  scalar * weighted_expectation law f.
Proof. induction law as [|[point weight] rest IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma weighted_expectation_zero {A} (law : list (A * R)) :
  weighted_expectation law (fun _ => 0) = 0.
Proof. induction law as [|[point weight] rest IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma weighted_expectation_mono {A} (law : list (A * R)) f g :
  nonnegative_law law -> (forall point, f point <= g point) ->
  weighted_expectation law f <= weighted_expectation law g.
Proof. intros Hlaw Hpoint; induction Hlaw as [|[point weight] rest Hweight Hrest IH];
  simpl in *; [lra| specialize (Hpoint point); nra]. Qed.
Lemma weighted_expectation_nonnegative {A} (law : list (A * R)) f :
  nonnegative_law law -> (forall point, 0 <= f point) ->
  0 <= weighted_expectation law f.
Proof. intros Hlaw Hpoint; rewrite <- (weighted_expectation_zero law).
  apply weighted_expectation_mono; assumption. Qed.
Lemma weighted_markov {A} (law : list (A * R)) event f threshold :
  nonnegative_law law -> 0 < threshold ->
  (forall point, 0 <= f point) ->
  (forall point, event point = true -> threshold <= f point) ->
  event_probability law event <= weighted_expectation law f / threshold.
Proof.
  intros Hlaw Hthreshold Hpositive Hdominates.
  assert (Hbound : threshold * event_probability law event <= weighted_expectation law f).
  { unfold event_probability. rewrite <- weighted_expectation_scale.
    apply weighted_expectation_mono; [exact Hlaw|].
    intros point; unfold indicator; destruct (event point) eqn:Hevent;
      [specialize (Hdominates point Hevent)|specialize (Hpositive point)]; nra. }
  apply (Rmult_le_reg_r threshold); [exact Hthreshold|].
  field_simplify; nra.
Qed.

Fixpoint real_sum (values : list R) : R :=
  match values with [] => 0 | value :: rest => value + real_sum rest end.
Lemma weighted_expectation_sum {A} (law : list (A * R)) {I : Type}
    (indices : list I) (observables : I -> A -> R) :
  weighted_expectation law (fun point => real_sum (map (fun index => observables index point) indices)) =
  real_sum (map (fun index => weighted_expectation law (observables index)) indices).
Proof. induction indices; simpl; [apply weighted_expectation_zero|].
  rewrite weighted_expectation_add, IHindices; reflexivity. Qed.
Lemma indicator_union_bound {A I : Type} (indices : list I)
    (events : I -> A -> bool) point :
  indicator (fun sample => existsb (fun index => events index sample) indices) point <=
  real_sum (map (fun index => indicator (events index) point) indices).
Proof.
  induction indices as [|index rest IH]; simpl; [unfold indicator; simpl; lra|].
  unfold indicator in *; simpl in *.
  destruct (events index point), (existsb (fun index => events index point) rest);
    simpl in *; lra.
Qed.
Theorem finite_union_bound {A I : Type} (law : list (A * R))
    (indices : list I) (events : I -> A -> bool) :
  nonnegative_law law ->
  event_probability law (fun point => existsb (fun index => events index point) indices) <=
  real_sum (map (fun index => event_probability law (events index)) indices).
Proof. intros Hlaw; unfold event_probability.
  rewrite <- weighted_expectation_sum.
  apply weighted_expectation_mono; [exact Hlaw|apply indicator_union_bound]. Qed.

Print Assumptions finite_union_bound.
Print Assumptions weighted_markov.

Lemma event_probability_monotone {A : Type} (law : list (A * R))
    (smaller larger : A -> bool) :
  nonnegative_law law ->
  (forall point, smaller point = true -> larger point = true) ->
  event_probability law smaller <= event_probability law larger.
Proof.
  intros Hlaw Hsubset; unfold event_probability.
  apply weighted_expectation_mono; [exact Hlaw|].
  intros point; unfold indicator.
  destruct (smaller point) eqn:Hsmaller.
  - rewrite (Hsubset point Hsmaller); lra.
  - destruct (larger point); lra.
Qed.
Print Assumptions event_probability_monotone.
