(** Data-dependent terminal-channel rejection and its finite-law error event.

    A rejection is sound whenever the four radius premises hold. The sampling
    model supplies simultaneous coverage; observing the retained counts does
    not turn that coverage into a posterior probability about fixed means. *)
From Stdlib Require Import Reals List Bool Lia Lra Psatz.
From OpenGororoba Require Import FiniteProbability FiniteBernoulliConcentration TerminalChannelSeparationReal.
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
