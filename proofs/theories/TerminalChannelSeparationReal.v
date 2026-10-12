(** Real-valued separation under a common stochastic binary channel.

    Deterministic radius premises and a positive separation margin exclude
    one common appended channel. Real foundations appear explicitly in the
    assumption reports. Statistical coverage, calibration and empirical
    stationarity belong to the experiment that supplies the premises. *)

From Stdlib Require Import Reals Psatz.
Open Scope R_scope.

Definition binary_channel (false_positive true_positive input_mean : R) : R :=
  false_positive * (1 - input_mean) + true_positive * input_mean.

Theorem binary_channel_contracts_separation :
  forall false_positive true_positive first_mean second_mean,
    0 <= false_positive <= 1 ->
    0 <= true_positive <= 1 ->
    Rabs (binary_channel false_positive true_positive first_mean -
          binary_channel false_positive true_positive second_mean) <=
    Rabs (first_mean - second_mean).
Proof.
  intros false_positive true_positive first_mean second_mean
    [false_positive_lower false_positive_upper]
    [true_positive_lower true_positive_upper].
  unfold binary_channel.
  replace
    (false_positive * (1 - first_mean) + true_positive * first_mean -
     (false_positive * (1 - second_mean) + true_positive * second_mean))
    with ((true_positive - false_positive) * (first_mean - second_mean))
    by ring.
  rewrite Rabs_mult.
  assert (slope_bound : Rabs (true_positive - false_positive) <= 1).
  { apply Rabs_le; split; lra. }
  pose proof (Rmult_le_compat_r (Rabs (first_mean - second_mean))
    (Rabs (true_positive - false_positive)) 1
    (Rabs_pos _) slope_bound) as multiplied_bound.
  lra.
Qed.

Lemma absolute_radius_bounds : forall value center radius,
  Rabs (value - center) <= radius ->
  center - radius <= value <= center + radius.
Proof.
  intros value center radius radius_bound.
  pose proof (Rle_abs (value - center)) as upper_bound.
  pose proof (Rle_abs (center - value)) as lower_bound.
  rewrite Rabs_minus_sym in lower_bound. split; lra.
Qed.

Theorem difference_radius_bound : forall first second first_center second_center first_radius second_radius,
  Rabs (first - first_center) <= first_radius ->
  Rabs (second - second_center) <= second_radius ->
  Rabs ((first - second) - (first_center - second_center)) <= first_radius + second_radius.
Proof.
  intros first second first_center second_center first_radius second_radius first_bound second_bound.
  apply absolute_radius_bounds in first_bound.
  apply absolute_radius_bounds in second_bound.
  destruct first_bound, second_bound. apply Rabs_le. split; lra.
Qed.

Theorem separation_radius_bound : forall first second first_center second_center first_radius second_radius,
  Rabs (first - first_center) <= first_radius ->
  Rabs (second - second_center) <= second_radius ->
  Rabs (first - second) <= Rabs (first_center - second_center) + first_radius + second_radius.
Proof.
  intros first second first_center second_center first_radius second_radius first_bound second_bound.
  pose proof (difference_radius_bound first second first_center second_center first_radius second_radius
    first_bound second_bound) as difference_bound.
  pose proof (Rabs_triang ((first - second) - (first_center - second_center))
    (first_center - second_center)) as triangle_bound.
  replace (((first - second) - (first_center - second_center)) +
    (first_center - second_center)) with (first - second) in triangle_bound by ring.
  lra.
Qed.

Theorem separated_centers_exclude_common_binary_channel : forall
  output_first output_second input_first input_second
  output_first_center output_second_center input_first_center input_second_center
  output_first_radius output_second_radius input_first_radius input_second_radius,
  Rabs (output_first - output_first_center) <= output_first_radius ->
  Rabs (output_second - output_second_center) <= output_second_radius ->
  Rabs (input_first - input_first_center) <= input_first_radius ->
  Rabs (input_second - input_second_center) <= input_second_radius ->
  Rabs (input_first_center - input_second_center) +
    output_first_radius + output_second_radius + input_first_radius + input_second_radius <
    Rabs (output_first_center - output_second_center) ->
  ~ exists false_positive true_positive,
    0 <= false_positive <= 1 /\ 0 <= true_positive <= 1 /\
    output_first = binary_channel false_positive true_positive input_first /\
    output_second = binary_channel false_positive true_positive input_second.
Proof.
  intros output_first output_second input_first input_second
    output_first_center output_second_center input_first_center input_second_center
    output_first_radius output_second_radius input_first_radius input_second_radius
    output_first_bound output_second_bound input_first_bound input_second_bound positive_margin
    [false_positive [true_positive
      [false_positive_bounds [true_positive_bounds [first_channel second_channel]]]]].
  pose proof (binary_channel_contracts_separation false_positive true_positive input_first input_second
    false_positive_bounds true_positive_bounds) as contraction.
  rewrite <- first_channel, <- second_channel in contraction.
  pose proof (separation_radius_bound input_first input_second input_first_center input_second_center
    input_first_radius input_second_radius input_first_bound input_second_bound) as input_upper_bound.
  rewrite Rabs_minus_sym in output_first_bound, output_second_bound.
  pose proof (separation_radius_bound output_first_center output_second_center output_first output_second
    output_first_radius output_second_radius output_first_bound output_second_bound) as output_lower_bound.
  lra.
Qed.

Print Assumptions binary_channel_contracts_separation.
Print Assumptions absolute_radius_bounds.
Print Assumptions difference_radius_bound.
Print Assumptions separation_radius_bound.
Print Assumptions separated_centers_exclude_common_binary_channel.
