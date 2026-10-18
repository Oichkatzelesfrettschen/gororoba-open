(** Declared estimator/look pairs share a finite simultaneous error budget.
    Marginal coverage comes from an external sampling-law proof. *)
From Stdlib Require Import Reals List Bool Lra.
From OpenGororoba Require Import FiniteProbability.
Import ListNotations.
Local Open Scope R_scope.

Lemma planned_sum_monotone {Index} (indices : list Index) first second :
  (forall index, In index indices -> first index <= second index) ->
  real_sum (map first indices) <= real_sum (map second indices).
Proof.
  induction indices as [|index rest induction_bound]; simpl; intros bound; [lra|].
  assert (head_bound : first index <= second index) by (apply bound; auto).
  assert (tail_bound : real_sum (map first rest) <= real_sum (map second rest)).
  { apply induction_bound. intros member included. apply bound. auto. }
  lra.
Qed.
Definition planned_failure {Sample Estimator Look}
    (declared : list (Estimator * Look)) (failure : Estimator * Look -> Sample -> bool) sample :=
  existsb (fun pair => failure pair sample) declared.
Theorem finite_planned_look_budget {Sample Estimator Look}
    (law : list (Sample * R)) (declared : list (Estimator * Look))
    (failure : Estimator * Look -> Sample -> bool)
    (allocation : Estimator * Look -> R) total_budget :
  nonnegative_law law ->
  (forall pair, In pair declared -> 0 <= allocation pair) ->
  (forall pair, In pair declared -> event_probability law (failure pair) <= allocation pair) ->
  real_sum (map allocation declared) <= total_budget ->
  event_probability law (planned_failure declared failure) <= total_budget.
Proof.
  intros nonnegative allocations marginal budget.
  eapply Rle_trans; [apply finite_union_bound; exact nonnegative|].
  eapply Rle_trans; [apply planned_sum_monotone; exact marginal|exact budget].
Qed.
Lemma planned_complement_probability {Sample} (law : list (Sample * R)) event :
  normalized_law law ->
  event_probability law (fun sample => negb (event sample)) = 1 - event_probability law event.
Proof.
  intros normalized.
  assert (split : weighted_expectation law (fun _ => 1) =
    event_probability law event + event_probability law (fun sample => negb (event sample))).
  { unfold event_probability. rewrite <- weighted_expectation_add.
    apply weighted_expectation_ext. intro sample. unfold indicator. destruct (event sample); simpl; ring. }
  unfold normalized_law in normalized. rewrite normalized in split. lra.
Qed.
Theorem finite_planned_simultaneous_coverage {Sample Estimator Look}
    (law : list (Sample * R)) (declared : list (Estimator * Look))
    (failure : Estimator * Look -> Sample -> bool) allocation total_budget :
  nonnegative_law law -> normalized_law law ->
  (forall pair, In pair declared -> 0 <= allocation pair) ->
  (forall pair, In pair declared -> event_probability law (failure pair) <= allocation pair) ->
  real_sum (map allocation declared) <= total_budget ->
  1 - total_budget <= event_probability law (fun sample => negb (planned_failure declared failure sample)).
Proof.
  intros nonnegative normalized allocations marginal budget.
  rewrite planned_complement_probability by exact normalized.
  pose proof (finite_planned_look_budget law declared failure allocation total_budget nonnegative allocations marginal budget). lra.
Qed.
Definition selected_look_failure {Sample Estimator Look}
    (selection : Sample -> option (Estimator * Look))
    (failure : Estimator * Look -> Sample -> bool) sample :=
  match selection sample with Some selected_pair => failure selected_pair sample | None => false end.
Theorem declared_selection_failure_subset {Sample Estimator Look}
    (declared : list (Estimator * Look)) selection failure :
  (forall sample pair, selection sample = Some pair -> In pair declared) ->
  forall sample, @selected_look_failure Sample Estimator Look selection failure sample = true ->
    planned_failure declared failure sample = true.
Proof.
  intros admitted sample selected. unfold selected_look_failure in selected.
  destruct (selection sample) as [pair|] eqn:chosen; [|discriminate].
  unfold planned_failure. apply existsb_exists. exists pair. split.
  - apply (admitted sample pair chosen).
  - exact selected.
Qed.
Theorem finite_declared_stopping_coverage {Sample Estimator Look}
    (law : list (Sample * R)) (declared : list (Estimator * Look))
    selection (failure : Estimator * Look -> Sample -> bool) allocation total_budget :
  nonnegative_law law ->
  (forall pair, In pair declared -> 0 <= allocation pair) ->
  (forall pair, In pair declared -> event_probability law (failure pair) <= allocation pair) ->
  real_sum (map allocation declared) <= total_budget ->
  (forall sample pair, selection sample = Some pair -> In pair declared) ->
  event_probability law (selected_look_failure selection failure) <= total_budget.
Proof.
  intros nonnegative allocations marginal budget admitted.
  eapply Rle_trans.
  - apply event_probability_monotone; [exact nonnegative|].
    apply declared_selection_failure_subset. exact admitted.
  - apply (finite_planned_look_budget law declared failure allocation total_budget); assumption.
Qed.

Definition omitted_look_law : list (unit * R) := [(tt,1)].
Definition omitted_look_failure (pair : nat * nat) (_ : unit) := Nat.eqb (snd pair) 1.
Example omitted_look_declared_probability :
  event_probability omitted_look_law (planned_failure [(0%nat,0%nat)] omitted_look_failure) = 0.
Proof. unfold event_probability, weighted_expectation, omitted_look_law, planned_failure, omitted_look_failure, indicator; simpl; ring. Qed.
Example omitted_look_selected_probability :
  event_probability omitted_look_law
    (selected_look_failure (fun _ => Some (0%nat,1%nat)) omitted_look_failure) = 1.
Proof. unfold event_probability, weighted_expectation, omitted_look_law, selected_look_failure, omitted_look_failure, indicator; simpl; ring. Qed.
Example omitted_look_exceeds_zero_budget :
  ~ event_probability omitted_look_law
    (selected_look_failure (fun _ => Some (0%nat,1%nat)) omitted_look_failure) <= 0.
Proof. rewrite omitted_look_selected_probability. lra. Qed.
Example invalid_marginal_allocation :
  ~ event_probability omitted_look_law (omitted_look_failure (0%nat,1%nat)) <= 0.
Proof. unfold event_probability, weighted_expectation, omitted_look_law, omitted_look_failure, indicator; simpl; lra. Qed.
Print Assumptions finite_planned_look_budget.
Print Assumptions finite_planned_simultaneous_coverage.
Print Assumptions finite_declared_stopping_coverage.
Print Assumptions omitted_look_exceeds_zero_budget.
