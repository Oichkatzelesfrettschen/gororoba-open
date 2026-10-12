(** Rational separation under a common stochastic binary channel.

    The affine slope lies between minus one and one. Four deterministic
    radius bounds therefore exclude a common appended channel when the
    center separation exceeds the replay separation and all four radii.
    Rational equalities use Qeq. Statistical coverage and empirical channel
    stability remain external premises. *)

From Stdlib Require Import QArith QArith.Qabs Lqa.
Open Scope Q_scope.

Definition binary_channel (false_positive true_positive input_mean : Q) : Q :=
  false_positive * (1 - input_mean) + true_positive * input_mean.

Theorem binary_channel_contracts_separation :
  forall false_positive true_positive first_mean second_mean,
    0 <= false_positive <= 1 ->
    0 <= true_positive <= 1 ->
    Qabs (binary_channel false_positive true_positive first_mean -
          binary_channel false_positive true_positive second_mean) <=
    Qabs (first_mean - second_mean).
Proof.
  intros false_positive true_positive first_mean second_mean
    [false_positive_lower false_positive_upper]
    [true_positive_lower true_positive_upper].
  unfold binary_channel.
  setoid_replace
    (false_positive * (1 - first_mean) + true_positive * first_mean -
     (false_positive * (1 - second_mean) + true_positive * second_mean))
    with ((true_positive - false_positive) * (first_mean - second_mean))
    by ring.
  rewrite Qabs_Qmult.
  assert (slope_bound : Qabs (true_positive - false_positive) <= 1).
  { apply Qabs_Qle_condition; split; lra. }
  pose proof (Qmult_le_compat_r _ _ (Qabs (first_mean - second_mean))
    slope_bound (Qabs_nonneg _)) as multiplied_bound.
  lra.
Qed.

Theorem difference_radius_bound : forall first second first_center second_center first_radius second_radius,
  Qabs (first - first_center) <= first_radius ->
  Qabs (second - second_center) <= second_radius ->
  Qabs ((first - second) - (first_center - second_center)) <= first_radius + second_radius.
Proof.
  intros first second first_center second_center first_radius second_radius first_bound second_bound.
  apply Qabs_Qle_condition in first_bound.
  apply Qabs_Qle_condition in second_bound.
  destruct first_bound, second_bound. apply Qabs_Qle_condition. split; lra.
Qed.

Theorem separation_radius_bound : forall first second first_center second_center first_radius second_radius,
  Qabs (first - first_center) <= first_radius ->
  Qabs (second - second_center) <= second_radius ->
  Qabs (first - second) <= Qabs (first_center - second_center) + first_radius + second_radius.
Proof.
  intros first second first_center second_center first_radius second_radius first_bound second_bound.
  pose proof (difference_radius_bound first second first_center second_center first_radius second_radius
    first_bound second_bound) as difference_bound.
  pose proof (Qabs_triangle ((first - second) - (first_center - second_center))
    (first_center - second_center)) as triangle_bound.
  setoid_replace (((first - second) - (first_center - second_center)) +
    (first_center - second_center)) with (first - second) in triangle_bound by ring.
  lra.
Qed.

Theorem separated_centers_exclude_common_binary_channel : forall
  output_first output_second input_first input_second
  output_first_center output_second_center input_first_center input_second_center
  output_first_radius output_second_radius input_first_radius input_second_radius,
  Qabs (output_first - output_first_center) <= output_first_radius ->
  Qabs (output_second - output_second_center) <= output_second_radius ->
  Qabs (input_first - input_first_center) <= input_first_radius ->
  Qabs (input_second - input_second_center) <= input_second_radius ->
  Qabs (input_first_center - input_second_center) +
    output_first_radius + output_second_radius + input_first_radius + input_second_radius <
    Qabs (output_first_center - output_second_center) ->
  ~ exists false_positive true_positive,
    0 <= false_positive <= 1 /\ 0 <= true_positive <= 1 /\
    output_first == binary_channel false_positive true_positive input_first /\
    output_second == binary_channel false_positive true_positive input_second.
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
  rewrite Qabs_Qminus in output_first_bound, output_second_bound.
  pose proof (separation_radius_bound output_first_center output_second_center output_first output_second
    output_first_radius output_second_radius output_first_bound output_second_bound) as output_lower_bound.
  lra.
Qed.

Print Assumptions binary_channel_contracts_separation.
Print Assumptions difference_radius_bound.
Print Assumptions separation_radius_bound.
Print Assumptions separated_centers_exclude_common_binary_channel.
