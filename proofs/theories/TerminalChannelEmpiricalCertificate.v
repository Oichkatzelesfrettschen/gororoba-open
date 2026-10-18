(** Data-dependent terminal-channel rejection and its finite-law error event.

    A rejection is sound whenever the four radius premises hold. The sampling
    model supplies simultaneous coverage; observing the retained counts does
    not turn that coverage into a posterior probability about fixed means. *)
From Stdlib Require Import Reals List Bool Lia Lra Psatz.
From OpenGororoba Require Import FinitePlannedLookCoverage FiniteProbability FiniteBernoulliConcentration TerminalChannelSeparationReal.
Import ListNotations.
Open Scope R_scope.

Definition terminal_radius : R := 21 / 1000.
Definition terminal_sample_count : R := 8192.
Definition terminal_family : list nat := seq 0 32.
Definition terminal_center {A} (parameters : nat -> R)
    (centered_sum : nat -> A -> R) (index : nat) (point : A) : R :=
  parameters index + centered_sum index point / terminal_sample_count.
Definition terminal_radius_failure {A} (centered_sum : nat -> A -> R)
    (index : nat) (point : A) : bool :=
  if Rle_dec (terminal_sample_count * terminal_radius)
      (Rabs (centered_sum index point)) then true else false.
Definition terminal_rejection {A} (parameters : nat -> R)
    (centered_sum : nat -> A -> R) (point : A) : bool :=
  if Rlt_dec
    (Rabs (terminal_center parameters centered_sum 2%nat point -
           terminal_center parameters centered_sum 3%nat point) + 4 * terminal_radius)
    (Rabs (terminal_center parameters centered_sum 0%nat point -
           terminal_center parameters centered_sum 1%nat point)) then true else false.
Definition common_terminal_channel (parameters : nat -> R) : Prop :=
  exists false_positive true_positive,
    0 <= false_positive <= 1 /\ 0 <= true_positive <= 1 /\
    parameters 0%nat = binary_channel false_positive true_positive (parameters 2%nat) /\
    parameters 1%nat = binary_channel false_positive true_positive (parameters 3%nat).

Lemma terminal_radius_from_centered_sum {A} parameters centered_sum index (point : A) :
  terminal_radius_failure centered_sum index point = false ->
  Rabs (parameters index - terminal_center parameters centered_sum index point) <= terminal_radius.
Proof.
  unfold terminal_radius_failure. destruct (Rle_dec _ _) as [large|small]; [discriminate|].
  intros _.
  pose proof (Rle_abs (centered_sum index point)) as upper.
  pose proof (Rle_abs (- centered_sum index point)) as lower.
  rewrite Rabs_Ropp in lower.
  unfold terminal_center, terminal_sample_count, terminal_radius in *.
  apply Rabs_le. split; lra.
Qed.

Theorem terminal_false_rejection_requires_radius_failure {A} parameters centered_sum (point : A) :
  common_terminal_channel parameters ->
  terminal_rejection parameters centered_sum point = true ->
  existsb (fun index => terminal_radius_failure centered_sum index point) terminal_family = true.
Proof.
  intros common rejected.
  destruct (existsb (fun index => terminal_radius_failure centered_sum index point) terminal_family)
    eqn:family_failure; [reflexivity|].
  assert (covered : forall index, (index < 4)%nat ->
    Rabs (parameters index - terminal_center parameters centered_sum index point) <= terminal_radius).
  { intros index index_bound. apply terminal_radius_from_centered_sum.
    destruct (terminal_radius_failure centered_sum index point) eqn:failure; [|reflexivity].
    assert (member : In index terminal_family).
    { unfold terminal_family. apply in_seq. lia. }
    assert (contradiction : existsb
      (fun position => terminal_radius_failure centered_sum position point) terminal_family = true).
    { apply existsb_exists. exists index. auto. }
    rewrite family_failure in contradiction. discriminate. }
  unfold terminal_rejection in rejected.
  destruct (Rlt_dec _ _) as [margin|]; [|discriminate].
  exfalso.
  apply (separated_centers_exclude_common_binary_channel
    (parameters 0%nat) (parameters 1%nat) (parameters 2%nat) (parameters 3%nat)
    (terminal_center parameters centered_sum 0%nat point)
    (terminal_center parameters centered_sum 1%nat point)
    (terminal_center parameters centered_sum 2%nat point)
    (terminal_center parameters centered_sum 3%nat point)
    terminal_radius terminal_radius terminal_radius terminal_radius).
  - apply covered; lia.
  - apply covered; lia.
  - apply covered; lia.
  - apply covered; lia.
  - lra.
  - exact common.
Qed.

Theorem terminal_false_rejection_probability {A} (law : list (A * R)) parameters centered_sum :
  nonnegative_law law ->
  common_terminal_channel parameters ->
  event_probability law
    (fun point => existsb (fun index => terminal_radius_failure centered_sum index point) terminal_family)
    <= 1 / 20 ->
  event_probability law (terminal_rejection parameters centered_sum) <= 1 / 20.
Proof.
  intros nonnegative common coverage.
  eapply Rle_trans; [|exact coverage].
  unfold event_probability. apply weighted_expectation_mono; [exact nonnegative|].
  intros point. unfold indicator.
  destruct (terminal_rejection parameters centered_sum point) eqn:rejected.
  - rewrite (terminal_false_rejection_requires_radius_failure parameters centered_sum point common rejected). lra.
  - destruct (existsb _ _); lra.
Qed.

(** The confidence procedure controls false rejections before data are seen.
    The first four marginals instantiate the channel test; all 32 marginals
    enter the declared simultaneous family. *)
Theorem terminal_32_mean_false_rejection {A} (law : list (A * R))
    (parameters : nat -> R) (centered_sum : nat -> A -> R) :
  nonnegative_law law -> normalized_law law ->
  (forall index, In index terminal_family -> 0 <= parameters index <= 1) ->
  (forall index, In index terminal_family -> forall observable,
    weighted_expectation law (fun point => observable (centered_sum index point)) =
    bernoulli_expectation terminal_samples (parameters index) observable) ->
  common_terminal_channel parameters ->
  event_probability law (terminal_rejection parameters centered_sum) <= 1 / 20.
Proof.
  intros nonnegative normalized bounded marginal common.
  apply terminal_false_rejection_probability; [exact nonnegative|exact common|].
  unfold terminal_radius_failure, terminal_sample_count, terminal_radius.
  apply (terminal_32_mean_family_coverage law terminal_family parameters centered_sum).
  - exact nonnegative.
  - exact normalized.
  - unfold terminal_family. rewrite length_seq. reflexivity.
  - exact bounded.
  - exact marginal.
Qed.

Definition retained_terminal_center (index : nat) : R :=
  match index with
  | 0%nat => 2964 / 8192
  | 1%nat => 4911 / 8192
  | 2%nat => 4067 / 8192
  | 3%nat => 4057 / 8192
  | _ => 0
  end.

Theorem retained_terminal_exact_margin :
  Rabs (retained_terminal_center 0%nat - retained_terminal_center 1%nat) -
  Rabs (retained_terminal_center 2%nat - retained_terminal_center 3%nat) -
  4 * terminal_radius = 156109 / 1024000.
Proof.
  unfold retained_terminal_center, terminal_radius.
  assert (hardware : Rabs (2964 / 8192 - 4911 / 8192) = 1947 / 8192).
  { rewrite Rabs_left; lra. }
  assert (replay : Rabs (4067 / 8192 - 4057 / 8192) = 10 / 8192).
  { rewrite Rabs_right; lra. }
  rewrite hardware, replay. field.
Qed.

Theorem retained_terminal_margin_positive :
  0 < Rabs (retained_terminal_center 0%nat - retained_terminal_center 1%nat) -
      Rabs (retained_terminal_center 2%nat - retained_terminal_center 3%nat) - 4 * terminal_radius.
Proof. rewrite retained_terminal_exact_margin. lra. Qed.

Print Assumptions terminal_false_rejection_requires_radius_failure.
Print Assumptions terminal_false_rejection_probability.
Print Assumptions retained_terminal_exact_margin.
Print Assumptions retained_terminal_margin_positive.

Print Assumptions terminal_32_mean_false_rejection.

(** Each radius belongs to its own mean; sampling procedures supply coverage. *)
Definition terminal_parameterized_rejection {Sample}
    (center : nat -> Sample -> R) (radius : nat -> R) sample :=
  if Rlt_dec
    (Rabs (center 2%nat sample - center 3%nat sample) +
      radius 0%nat + radius 1%nat + radius 2%nat + radius 3%nat)
    (Rabs (center 0%nat sample - center 1%nat sample)) then true else false.
Definition terminal_parameterized_radius_failure {Sample} parameters
    (center : nat -> Sample -> R) (radius : nat -> R) index sample :=
  if Rlt_dec (radius index) (Rabs (parameters index - center index sample)) then true else false.
Theorem terminal_parameterized_deterministic_certificate {Sample} parameters center radius (sample : Sample) :
  (forall index, (index < 4)%nat -> Rabs (parameters index - center index sample) <= radius index) ->
  terminal_parameterized_rejection center radius sample = true ->
  ~ common_terminal_channel parameters.
Proof.
  intros covered rejected common. unfold terminal_parameterized_rejection in rejected.
  destruct (Rlt_dec _ _) as [margin|]; [|discriminate].
  apply (separated_centers_exclude_common_binary_channel
    (parameters 0%nat) (parameters 1%nat) (parameters 2%nat) (parameters 3%nat)
    (center 0%nat sample) (center 1%nat sample) (center 2%nat sample) (center 3%nat sample)
    (radius 0%nat) (radius 1%nat) (radius 2%nat) (radius 3%nat));
    try (apply covered; lia); assumption.
Qed.
Theorem terminal_parameterized_false_rejection {Sample} parameters center radius (sample : Sample) :
  common_terminal_channel parameters -> terminal_parameterized_rejection center radius sample = true ->
  exists index, (index < 4)%nat /\ terminal_parameterized_radius_failure parameters center radius index sample = true.
Proof.
  intros common rejected.
  destruct (existsb (fun index => terminal_parameterized_radius_failure parameters center radius index sample) (seq 0 4)) eqn:failure.
  - apply existsb_exists in failure. destruct failure as [index [member event]].
    exists index. split; [apply in_seq in member; lia|exact event].
  - exfalso. apply (terminal_parameterized_deterministic_certificate parameters center radius sample); [|exact rejected|exact common].
    intros index bounded.
    destruct (Rlt_dec (radius index) (Rabs (parameters index - center index sample))) as [outside|inside]; [|lra].
    assert (witness : existsb (fun position => terminal_parameterized_radius_failure parameters center radius position sample) (seq 0 4) = true).
    { apply existsb_exists. exists index. split; [apply in_seq; lia|].
      unfold terminal_parameterized_radius_failure. destruct (Rlt_dec _ _); [reflexivity|contradiction]. }
    rewrite failure in witness. discriminate.
Qed.
Theorem terminal_parameterized_probability {Sample} (law : list (Sample * R))
    parameters center radius (declared : list nat) total_budget :
  nonnegative_law law -> common_terminal_channel parameters ->
  (forall index, (index < 4)%nat -> In index declared) ->
  event_probability law (fun sample => existsb
    (fun index => terminal_parameterized_radius_failure parameters center radius index sample) declared) <= total_budget ->
  event_probability law (terminal_parameterized_rejection center radius) <= total_budget.
Proof.
  intros nonnegative common included coverage. eapply Rle_trans; [|exact coverage].
  apply event_probability_monotone; [exact nonnegative|]. intros sample rejected.
  destruct (terminal_parameterized_false_rejection parameters center radius sample common rejected) as [index [bounded failure]].
  apply existsb_exists. exists index. split; [apply included; exact bounded|exact failure].
Qed.
Definition terminal_selected_rejection {Sample Look}
    (selection : Sample -> option Look) (center : Look -> nat -> Sample -> R)
    (radius : Look -> nat -> R) sample :=
  match selection sample with Some look => terminal_parameterized_rejection (center look) (radius look) sample | None => false end.
Theorem terminal_planned_false_rejection_probability {Sample Look}
    (law : list (Sample * R)) parameters (declared : list (nat * Look))
    selection (center : Look -> nat -> Sample -> R) (radius : Look -> nat -> R) allocation total_budget :
  nonnegative_law law -> common_terminal_channel parameters ->
  (forall pair, In pair declared -> 0 <= allocation pair) ->
  (forall pair, In pair declared ->
    event_probability law (terminal_parameterized_radius_failure parameters (center (snd pair)) (radius (snd pair)) (fst pair)) <= allocation pair) ->
  real_sum (map allocation declared) <= total_budget ->
  (forall sample look, selection sample = Some look -> forall index, (index < 4)%nat -> In (index,look) declared) ->
  event_probability law (terminal_selected_rejection selection center radius) <= total_budget.
Proof.
  intros nonnegative common allocations marginal budget admitted.
  eapply Rle_trans with (r2 := event_probability law (planned_failure declared
    (fun pair => terminal_parameterized_radius_failure parameters (center (snd pair)) (radius (snd pair)) (fst pair)))).
  - apply event_probability_monotone; [exact nonnegative|]. intros sample rejected.
    unfold terminal_selected_rejection in rejected. destruct (selection sample) as [look|] eqn:chosen; [|discriminate].
    destruct (terminal_parameterized_false_rejection parameters (center look) (radius look) sample common rejected)
      as [index [bounded failure]].
    unfold planned_failure. apply existsb_exists. exists (index,look). split.
    + exact (admitted sample look chosen index bounded).
    + exact failure.
  - apply (finite_planned_look_budget law declared
      (fun pair => terminal_parameterized_radius_failure parameters (center (snd pair)) (radius (snd pair)) (fst pair)) allocation total_budget); assumption.
Qed.
Theorem terminal_historical_rejection_specialization {Sample} parameters centered_sum (sample : Sample) :
  terminal_rejection parameters centered_sum sample =
  terminal_parameterized_rejection (terminal_center parameters centered_sum) (fun _ => terminal_radius) sample.
Proof.
  unfold terminal_rejection, terminal_parameterized_rejection.
  replace (Rabs (terminal_center parameters centered_sum 2%nat sample - terminal_center parameters centered_sum 3%nat sample) +
    terminal_radius + terminal_radius + terminal_radius + terminal_radius)
    with (Rabs (terminal_center parameters centered_sum 2%nat sample - terminal_center parameters centered_sum 3%nat sample) + 4 * terminal_radius) by ring.
  reflexivity.
Qed.
Theorem terminal_historical_radius_specialization {Sample} parameters centered_sum index (sample : Sample) :
  terminal_radius_failure centered_sum index sample = false ->
  terminal_parameterized_radius_failure parameters (terminal_center parameters centered_sum) (fun _ => terminal_radius) index sample = false.
Proof.
  intro covered. apply (terminal_radius_from_centered_sum parameters centered_sum index sample) in covered.
  unfold terminal_parameterized_radius_failure. destruct (Rlt_dec _ _); [lra|reflexivity].
Qed.
Theorem retained_terminal_parameterized_exact_margin :
  Rabs (retained_terminal_center 0%nat - retained_terminal_center 1%nat) -
  (Rabs (retained_terminal_center 2%nat - retained_terminal_center 3%nat) +
    terminal_radius + terminal_radius + terminal_radius + terminal_radius) = 156109 / 1024000.
Proof.
  replace (Rabs (retained_terminal_center 0%nat - retained_terminal_center 1%nat) -
    (Rabs (retained_terminal_center 2%nat - retained_terminal_center 3%nat) +
      terminal_radius + terminal_radius + terminal_radius + terminal_radius))
    with (Rabs (retained_terminal_center 0%nat - retained_terminal_center 1%nat) -
      Rabs (retained_terminal_center 2%nat - retained_terminal_center 3%nat) - 4 * terminal_radius) by ring.
  exact retained_terminal_exact_margin.
Qed.
Print Assumptions terminal_parameterized_deterministic_certificate.
Print Assumptions terminal_parameterized_false_rejection.
Print Assumptions terminal_parameterized_probability.
Print Assumptions terminal_planned_false_rejection_probability.
Print Assumptions terminal_historical_rejection_specialization.
Print Assumptions terminal_historical_radius_specialization.
Print Assumptions retained_terminal_parameterized_exact_margin.

Corollary terminal_historical_32_mean_specialization {Sample} (law : list (Sample * R)) parameters centered_sum :
  nonnegative_law law -> normalized_law law ->
  (forall index, In index terminal_family -> 0 <= parameters index <= 1) ->
  (forall index, In index terminal_family -> forall observable,
    weighted_expectation law (fun sample => observable (centered_sum index sample)) =
    bernoulli_expectation terminal_samples (parameters index) observable) ->
  common_terminal_channel parameters ->
  event_probability law
    (terminal_parameterized_rejection (terminal_center parameters centered_sum) (fun _ => terminal_radius)) <= 1 / 20.
Proof.
  intros nonnegative normalized bounded marginal common.
  replace (event_probability law
    (terminal_parameterized_rejection (terminal_center parameters centered_sum) (fun _ => terminal_radius)))
    with (event_probability law (terminal_rejection parameters centered_sum)).
  - apply terminal_32_mean_false_rejection; assumption.
  - unfold event_probability. apply weighted_expectation_ext. intro sample.
    unfold indicator. rewrite terminal_historical_rejection_specialization. reflexivity.
Qed.
Example terminal_historical_fixture_parameters :
  terminal_sample_count = 8192 /\ length terminal_family = 32%nat /\ terminal_radius = 21 / 1000.
Proof. repeat split; reflexivity. Qed.
Print Assumptions terminal_historical_32_mean_specialization.
Print Assumptions terminal_historical_fixture_parameters.
