(** Assignment precedes feedback: the recorded bit selects the work channel. *)
From Stdlib Require Import Reals List Bool Lra FunctionalExtensionality.
From OpenGororoba Require Import BranchSignedCoherence FourStateMatrixAlgebra.
Import ListNotations.
Local Open Scope R_scope.
Definition kraus_effect (operators : list Matrix) :=
  work_matrix_sum (map (fun operator => work_product (work_adjoint operator) operator) operators).
Definition kraus_map (operators : list Matrix) density :=
  work_matrix_sum (map (fun operator => work_congruence operator density) operators).
Definition kraus_complete operators := kraus_effect operators = work_identity.
Lemma kraus_map_positive : forall operators density,
  positive_semidefinite density -> positive_semidefinite (kraus_map operators density).
Proof.
  intros operators density positive. apply work_matrix_sum_positive.
  apply Forall_forall. intros branch member. apply in_map_iff in member.
  destruct member as [operator [equal member]]. subst branch. apply work_congruence_positive. exact positive.
Qed.
Lemma kraus_map_trace : forall operators density,
  work_trace (kraus_map operators density) = work_trace (work_product (kraus_effect operators) density).
Proof.
  induction operators as [|operator rest induction_trace]; intro density.
  - unfold kraus_map, kraus_effect; simpl. rewrite work_product_zero_left. reflexivity.
  - change (work_trace (work_matrix_add (work_congruence operator density) (kraus_map rest density)) =
      work_trace (work_product (work_matrix_add (work_product (work_adjoint operator) operator) (kraus_effect rest)) density)).
    rewrite work_product_add_left, !work_trace_add, work_congruence_trace, induction_trace. reflexivity.
Qed.
Theorem complete_kraus_trace_preserving : forall operators density,
  kraus_complete operators -> work_trace (kraus_map operators density) = work_trace density.
Proof. intros operators density complete. rewrite kraus_map_trace. unfold kraus_complete in complete. rewrite complete, work_product_identity_left. reflexivity. Qed.
Lemma kraus_map_zero : forall operators, kraus_map operators work_zero = work_zero.
Proof.
  induction operators; [reflexivity|]. change (work_matrix_add (work_congruence a work_zero) (kraus_map operators work_zero) = work_zero).
  rewrite work_congruence_zero, IHoperators. apply work_matrix_ext. intros row column.
  apply complex_ext; unfold work_matrix_add, work_zero, zero, add; simpl; ring.
Qed.
Lemma kraus_map_add : forall operators first second,
  kraus_map operators (work_matrix_add first second) = work_matrix_add (kraus_map operators first) (kraus_map operators second).
Proof.
  induction operators; intros.
  - apply work_matrix_ext. intros row column. apply complex_ext; unfold kraus_map, work_matrix_sum, work_matrix_add, work_zero, zero, add; simpl; ring.
  - change (work_matrix_add (work_congruence a (work_matrix_add first second)) (kraus_map operators (work_matrix_add first second)) =
      work_matrix_add (work_matrix_add (work_congruence a first) (kraus_map operators first))
        (work_matrix_add (work_congruence a second) (kraus_map operators second))).
    rewrite work_congruence_add, IHoperators. apply work_matrix_ext. intros row column.
    apply complex_ext; unfold work_matrix_add, add; simpl; ring.
Qed.
Lemma kraus_map_scale : forall operators factor density,
  kraus_map operators (work_matrix_scale factor density) = work_matrix_scale factor (kraus_map operators density).
Proof.
  induction operators; intros.
  - apply work_matrix_ext. intros row column. apply complex_ext; unfold kraus_map, work_matrix_sum, work_matrix_scale, work_zero, zero, scale; simpl; ring.
  - change (work_matrix_add (work_congruence a (work_matrix_scale factor density)) (kraus_map operators (work_matrix_scale factor density)) =
      work_matrix_scale factor (work_matrix_add (work_congruence a density) (kraus_map operators density))).
    rewrite work_congruence_scale, IHoperators. apply work_matrix_ext. intros row column.
    apply complex_ext; unfold work_matrix_add, work_matrix_scale, scale, add; simpl; ring.
Qed.
Lemma kraus_map_sum : forall operators densities,
  kraus_map operators (work_matrix_sum densities) = work_matrix_sum (map (kraus_map operators) densities).
Proof. intros operators densities. induction densities; simpl; [apply kraus_map_zero|]. rewrite kraus_map_add, IHdensities. reflexivity. Qed.

Section FiniteInstrument.
Context {Outcome : Type}.
Variable outcomes : list Outcome.
Variable measurement : Outcome -> list Matrix.
Variable assignment : bool -> Outcome -> R.
Variable feedback : bool -> list Matrix.
Definition measurement_effect := work_matrix_sum (map (fun outcome => kraus_effect (measurement outcome)) outcomes).
Definition measurement_complete := measurement_effect = work_identity.
Definition assignment_stochastic := forall outcome, In outcome outcomes ->
  0 <= assignment false outcome /\ 0 <= assignment true outcome /\ assignment false outcome + assignment true outcome = 1.
Definition assigned_branch density recorded :=
  work_matrix_sum (map (fun outcome => work_matrix_scale (assignment recorded outcome) (kraus_map (measurement outcome) density)) outcomes).
Definition recorded_feedback_branch density recorded := kraus_map (feedback recorded) (assigned_branch density recorded).
Definition explicit_feedback_branch density recorded :=
  work_matrix_sum (map (fun outcome => work_matrix_scale (assignment recorded outcome)
    (kraus_map (feedback recorded) (kraus_map (measurement outcome) density))) outcomes).
Theorem recorded_feedback_branch_summation : forall density recorded,
  recorded_feedback_branch density recorded = explicit_feedback_branch density recorded.
Proof.
  intros density recorded. unfold recorded_feedback_branch, assigned_branch, explicit_feedback_branch.
  rewrite kraus_map_sum, map_map. f_equal. apply map_ext. intro outcome. apply kraus_map_scale.
Qed.
Theorem assigned_branch_positive : forall density recorded,
  assignment_stochastic -> positive_semidefinite density -> positive_semidefinite (assigned_branch density recorded).
Proof.
  intros density recorded stochastic positive. apply work_matrix_sum_positive. apply Forall_forall.
  intros branch member. apply in_map_iff in member. destruct member as [outcome [equal included]]. subst branch.
  apply work_positive_scale; [destruct recorded; specialize (stochastic outcome included); tauto|apply kraus_map_positive; exact positive].
Qed.
Theorem recorded_feedback_branch_positive : forall density recorded,
  assignment_stochastic -> positive_semidefinite density -> positive_semidefinite (recorded_feedback_branch density recorded).
Proof. intros. apply kraus_map_positive, assigned_branch_positive; assumption. Qed.
Lemma measurement_trace_sum : forall density,
  work_trace (work_matrix_sum (map (fun outcome => kraus_map (measurement outcome) density) outcomes)) =
  work_trace (work_product measurement_effect density).
Proof.
  intro density. unfold measurement_effect. induction outcomes as [|outcome rest induction_trace].
  - simpl. rewrite work_product_zero_left. reflexivity.
  - simpl. rewrite work_product_add_left, !work_trace_add, kraus_map_trace, induction_trace. reflexivity.
Qed.
Lemma assigned_branch_trace_sum : forall density,
  assignment_stochastic ->
  add (work_trace (assigned_branch density false)) (work_trace (assigned_branch density true)) =
  work_trace (work_matrix_sum (map (fun outcome => kraus_map (measurement outcome) density) outcomes)).
Proof.
  intro density. unfold assignment_stochastic, assigned_branch. induction outcomes as [|outcome rest induction_trace]; intro stochastic.
  - simpl. rewrite work_trace_zero. apply complex_ext; unfold add, zero; simpl; ring.
  - simpl. rewrite !work_trace_add, !work_trace_scale.
    assert (tail_stochastic : forall item, In item rest ->
      0 <= assignment false item /\ 0 <= assignment true item /\ assignment false item + assignment true item = 1).
    { intros item included. apply stochastic. right. exact included. }
    specialize (induction_trace tail_stochastic). specialize (stochastic outcome (or_introl eq_refl)).
    apply complex_ext.
    + apply (f_equal real_part) in induction_trace. unfold add, scale in *; simpl in *. destruct stochastic as [_ [_ total]]. nra.
    + apply (f_equal imag_part) in induction_trace. unfold add, scale in *; simpl in *. destruct stochastic as [_ [_ total]]. nra.
Qed.
Theorem recorded_feedback_trace_preserving : forall density,
  assignment_stochastic -> measurement_complete ->
  (forall recorded, kraus_complete (feedback recorded)) ->
  add (work_trace (recorded_feedback_branch density false)) (work_trace (recorded_feedback_branch density true)) = work_trace density.
Proof.
  intros density stochastic complete feedback_complete. unfold recorded_feedback_branch.
  rewrite !complete_kraus_trace_preserving by apply feedback_complete.
  rewrite assigned_branch_trace_sum by exact stochastic.
  rewrite measurement_trace_sum. unfold measurement_complete in complete.
  rewrite complete, work_product_identity_left. reflexivity.
Qed.
Definition recorded_feedback_joint density :=
  recorded_matrix (recorded_feedback_branch density false) (recorded_feedback_branch density true).
Theorem recorded_feedback_joint_blocks : forall density recorded row column,
  recorded_feedback_joint density recorded row recorded column = explicit_feedback_branch density recorded row column.
Proof.
  intros density [] row column; unfold recorded_feedback_joint, recorded_matrix; simpl;
    rewrite recorded_feedback_branch_summation; reflexivity.
Qed.
End FiniteInstrument.
Print Assumptions kraus_map_positive.
Print Assumptions complete_kraus_trace_preserving.
Print Assumptions recorded_feedback_branch_summation.
Print Assumptions recorded_feedback_branch_positive.
Print Assumptions recorded_feedback_trace_preserving.
Print Assumptions recorded_feedback_joint_blocks.

Definition recorded_quadratic
    (joint : bool -> Basis -> bool -> Basis -> Complex)
    (vector : bool -> Basis -> Complex) :=
  add
    (sum_basis (fun row => add
      (sum_basis (fun column => multiply (conjugate (vector false row)) (multiply (joint false row false column) (vector false column))))
      (sum_basis (fun column => multiply (conjugate (vector false row)) (multiply (joint false row true column) (vector true column))))))
    (sum_basis (fun row => add
      (sum_basis (fun column => multiply (conjugate (vector true row)) (multiply (joint true row false column) (vector false column))))
      (sum_basis (fun column => multiply (conjugate (vector true row)) (multiply (joint true row true column) (vector true column)))))).
Definition recorded_positive (joint : bool -> Basis -> bool -> Basis -> Complex) :=
  (forall left row right column, joint left row right column = conjugate (joint right column left row)) /\
  forall vector, 0 <= real_part (recorded_quadratic joint vector).
Lemma recorded_block_quadratic : forall branch_zero branch_one vector,
  recorded_quadratic (recorded_matrix branch_zero branch_one) vector =
  add (quadratic_form branch_zero (vector false)) (quadratic_form branch_one (vector true)).
Proof.
  intros; apply complex_ext; unfold recorded_quadratic, recorded_matrix, quadratic_form, sum_basis, add, multiply, conjugate, zero; simpl; ring.
Qed.
Theorem recorded_block_positive : forall branch_zero branch_one,
  positive_semidefinite branch_zero -> positive_semidefinite branch_one ->
  recorded_positive (recorded_matrix branch_zero branch_one).
Proof.
  intros branch_zero branch_one [zero_hermitian zero_positive] [one_hermitian one_positive]. split.
  - intros [] row [] column; unfold recorded_matrix; simpl; try apply zero_hermitian; try apply one_hermitian;
      apply complex_ext; unfold conjugate, zero; simpl; ring.
  - intro vector. rewrite recorded_block_quadratic.
    specialize (zero_positive (vector false)). specialize (one_positive (vector true)). cbn [real_part add]. lra.
Qed.
Theorem recorded_feedback_joint_positive {Outcome} (outcomes : list Outcome) measurement assignment feedback density :
  assignment_stochastic outcomes assignment -> positive_semidefinite density ->
  recorded_positive (recorded_feedback_joint outcomes measurement assignment feedback density).
Proof. intros stochastic positive. apply recorded_block_positive; apply recorded_feedback_branch_positive; assumption. Qed.
Theorem recorded_feedback_subnormalized {Outcome} (outcomes : list Outcome) measurement assignment feedback density recorded :
  assignment_stochastic outcomes assignment -> measurement_complete outcomes measurement ->
  (forall bit, kraus_complete (feedback bit)) -> subnormalized_density density ->
  subnormalized_density (recorded_feedback_branch outcomes measurement assignment feedback density recorded).
Proof.
  intros stochastic complete feedback_complete [positive input_trace].
  assert (zero_positive : positive_semidefinite (recorded_feedback_branch outcomes measurement assignment feedback density false))
    by (apply recorded_feedback_branch_positive; assumption).
  assert (one_positive : positive_semidefinite (recorded_feedback_branch outcomes measurement assignment feedback density true))
    by (apply recorded_feedback_branch_positive; assumption).
  pose proof (work_positive_trace_nonnegative _ zero_positive) as zero_trace.
  pose proof (work_positive_trace_nonnegative _ one_positive) as one_trace.
  pose proof (recorded_feedback_trace_preserving outcomes measurement assignment feedback density stochastic complete feedback_complete) as total.
  apply (f_equal real_part) in total. cbn [real_part add] in total.
  change (0 <= real_part (work_trace density) <= 1) in input_trace.
  destruct recorded.
  - split; [exact one_positive|].
    change (0 <= real_part (work_trace (recorded_feedback_branch outcomes measurement assignment feedback density true)) <= 1). lra.
  - split; [exact zero_positive|].
    change (0 <= real_part (work_trace (recorded_feedback_branch outcomes measurement assignment feedback density false)) <= 1). lra.
Qed.
Theorem recorded_feedback_pauli_estimator {Outcome} (outcomes : list Outcome) measurement assignment feedback density :
  assignment_stochastic outcomes assignment -> measurement_complete outcomes measurement ->
  (forall bit, kraus_complete (feedback bit)) -> subnormalized_density density ->
  reconstructed_coherence (recorded_signed_block
    (recorded_feedback_branch outcomes measurement assignment feedback density false)
    (recorded_feedback_branch outcomes measurement assignment feedback density true)) =
  subtract (explicit_feedback_branch outcomes measurement assignment feedback density false ket01 ket10)
    (explicit_feedback_branch outcomes measurement assignment feedback density true ket01 ket10).
Proof.
  intros stochastic complete feedback_complete positive.
  rewrite recorded_signed_difference.
  rewrite (branch_signed_entry _ _ (recorded_feedback_subnormalized outcomes measurement assignment feedback density false stochastic complete feedback_complete positive)
    (recorded_feedback_subnormalized outcomes measurement assignment feedback density true stochastic complete feedback_complete positive)).
  rewrite !recorded_feedback_branch_summation. reflexivity.
Qed.
Print Assumptions recorded_feedback_joint_positive.
Print Assumptions recorded_feedback_subnormalized.
Print Assumptions recorded_feedback_pauli_estimator.

Definition binary_assignment (zero_to_one one_to_zero : R) (recorded outcome : bool) :=
  if outcome then (if recorded then 1-one_to_zero else one_to_zero)
  else (if recorded then zero_to_one else 1-zero_to_one).
Lemma binary_assignment_stochastic : forall zero_to_one one_to_zero,
  0 <= zero_to_one <= 1 -> 0 <= one_to_zero <= 1 ->
  assignment_stochastic [false;true] (binary_assignment zero_to_one one_to_zero).
Proof. intros zero_to_one one_to_zero zero_bounds one_bounds [] included; unfold binary_assignment; repeat split; lra. Qed.
Theorem binary_assignment_before_feedback : forall measurement zero_to_one one_to_zero density,
  assigned_branch [false;true] measurement (binary_assignment zero_to_one one_to_zero) density false =
    asymmetric_assigned_zero zero_to_one one_to_zero (kraus_map (measurement false) density) (kraus_map (measurement true) density) /\
  assigned_branch [false;true] measurement (binary_assignment zero_to_one one_to_zero) density true =
    asymmetric_assigned_one zero_to_one one_to_zero (kraus_map (measurement false) density) (kraus_map (measurement true) density).
Proof.
  intros. split; apply work_matrix_ext; intros row column; apply complex_ext;
    unfold assigned_branch, binary_assignment, work_matrix_sum, work_matrix_add, work_matrix_scale,
      asymmetric_assigned_zero, asymmetric_assigned_one, work_zero, zero, add, scale; simpl; ring.
Qed.
Lemma kraus_singleton : forall operator density, kraus_map [operator] density = work_congruence operator density.
Proof. intros. unfold kraus_map. simpl. apply (proj1 (work_matrix_add_zero _)). Qed.
Lemma kraus_identity : forall density, kraus_map [work_identity] density = density.
Proof. intros. rewrite kraus_singleton. unfold work_congruence. rewrite work_adjoint_identity, work_product_identity_left, work_product_identity_right. reflexivity. Qed.
Definition feedback_flip_basis basis := match basis with ket00 => ket10 | ket01 => ket11 | ket10 => ket00 | ket11 => ket01 end.
Definition feedback_flip_operator : Matrix := fun row column => if work_basis_equal row (feedback_flip_basis column) then one else zero.
Definition feedback_counterexample_density : Matrix := fun row column =>
  if andb (work_basis_equal row ket00) (work_basis_equal column ket00) then one else zero.
Definition feedback_counterexample_measurement (outcome : bool) := if outcome then [] else [work_identity].
Definition feedback_counterexample_channels (recorded : bool) := if recorded then [feedback_flip_operator] else [work_identity].
Lemma feedback_flip_complete : kraus_complete [feedback_flip_operator].
Proof.
  unfold kraus_complete, kraus_effect. simpl.
  rewrite (proj1 (work_matrix_add_zero _)). apply work_matrix_ext.
  intros row column; destruct row, column; apply complex_ext;
    unfold work_product, work_adjoint, feedback_flip_operator, feedback_flip_basis,
      work_identity, work_basis_equal, sum_basis, add, multiply, conjugate, one, zero; simpl; ring.
Qed.
Lemma feedback_identity_complete : kraus_complete [work_identity].
Proof.
  unfold kraus_complete, kraus_effect. simpl. rewrite (proj1 (work_matrix_add_zero _)), work_adjoint_identity, work_product_identity_left. reflexivity.
Qed.
Lemma feedback_counterexample_complete :
  measurement_complete [false;true] feedback_counterexample_measurement /\
  (forall recorded, kraus_complete (feedback_counterexample_channels recorded)).
Proof.
  split.
  - unfold measurement_complete, measurement_effect, feedback_counterexample_measurement.
    change (work_matrix_add (kraus_effect [work_identity]) (work_matrix_add work_zero work_zero) = work_identity).
    rewrite (proj1 (work_matrix_add_zero _)), (proj1 (work_matrix_add_zero _)). exact feedback_identity_complete.
  - intros []; [apply feedback_flip_complete|apply feedback_identity_complete].
Qed.
Lemma feedback_counterexample_density_normalized :
  subnormalized_density feedback_counterexample_density /\ work_trace feedback_counterexample_density = one.
Proof.
  assert (positive : positive_semidefinite feedback_counterexample_density).
  { split.
    - intros row column; destruct row, column; apply complex_ext;
        unfold feedback_counterexample_density, work_basis_equal, one, zero, conjugate; simpl; ring.
    - intro vector. unfold quadratic_form, feedback_counterexample_density, work_basis_equal,
        sum_basis, add, multiply, conjugate, one, zero; simpl; nra. }
  assert (trace : work_trace feedback_counterexample_density = one).
  { apply complex_ext; unfold work_trace, feedback_counterexample_density, work_basis_equal, sum_basis, add, one, zero; simpl; ring. }
  split; [split; [exact positive|]|exact trace]. change (0 <= real_part (work_trace feedback_counterexample_density) <= 1).
  rewrite trace. simpl. lra.
Qed.
Lemma feedback_counterexample_assigned_true :
  assigned_branch [false;true] feedback_counterexample_measurement (binary_assignment 1 1) feedback_counterexample_density true = feedback_counterexample_density.
Proof.
  unfold assigned_branch, feedback_counterexample_measurement, binary_assignment.
  change (work_matrix_add (work_matrix_scale 1 (kraus_map [work_identity] feedback_counterexample_density))
    (work_matrix_add (work_matrix_scale (1-1) work_zero) work_zero) = feedback_counterexample_density).
  rewrite kraus_identity, work_matrix_scale_one, work_matrix_scale_of_zero, !(proj1 (work_matrix_add_zero _)). reflexivity.
Qed.
Definition true_outcome_feedback_branch {Outcome} (outcomes : list Outcome) (measurement : Outcome -> list Matrix) (assignment : bool -> Outcome -> R)
    (feedback : Outcome -> list Matrix) (density : Matrix) (recorded : bool) :=
  work_matrix_sum (map (fun outcome => work_matrix_scale (assignment recorded outcome)
    (kraus_map (feedback outcome) (kraus_map (measurement outcome) density))) outcomes).
Theorem recorded_bit_feedback_counterexample :
  recorded_feedback_branch [false;true] feedback_counterexample_measurement (binary_assignment 1 1)
    feedback_counterexample_channels feedback_counterexample_density true ket10 ket10 = one /\
  true_outcome_feedback_branch [false;true] feedback_counterexample_measurement (binary_assignment 1 1)
    feedback_counterexample_channels feedback_counterexample_density true ket10 ket10 = zero.
Proof.
  split.
  - unfold recorded_feedback_branch. rewrite feedback_counterexample_assigned_true.
    change (kraus_map [feedback_flip_operator] feedback_counterexample_density ket10 ket10 = one).
    rewrite kraus_singleton. apply complex_ext; unfold work_congruence, work_product, work_adjoint,
      feedback_flip_operator, feedback_flip_basis, feedback_counterexample_density, work_basis_equal,
      sum_basis, add, multiply, conjugate, one, zero; simpl; ring.
  - unfold true_outcome_feedback_branch, feedback_counterexample_measurement, feedback_counterexample_channels, binary_assignment.
    change (work_matrix_add (work_matrix_scale 1 (kraus_map [work_identity] (kraus_map [work_identity] feedback_counterexample_density)))
      (work_matrix_add (work_matrix_scale (1-1) (kraus_map [feedback_flip_operator] work_zero)) work_zero) ket10 ket10 = zero).
    rewrite !kraus_identity, kraus_map_zero, work_matrix_scale_of_zero, work_matrix_scale_one, !(proj1 (work_matrix_add_zero _)). reflexivity.
Qed.
Theorem recorded_bit_feedback_differs_from_true_outcome :
  recorded_feedback_branch [false;true] feedback_counterexample_measurement (binary_assignment 1 1)
    feedback_counterexample_channels feedback_counterexample_density true <>
  true_outcome_feedback_branch [false;true] feedback_counterexample_measurement (binary_assignment 1 1)
    feedback_counterexample_channels feedback_counterexample_density true.
Proof.
  intro equal. pose proof (f_equal (fun density => density ket10 ket10) equal) as entry.
  destruct recorded_bit_feedback_counterexample as [recorded true_outcome]. cbn beta in entry. rewrite recorded, true_outcome in entry.
  apply (f_equal real_part) in entry. simpl in entry. lra.
Qed.
Print Assumptions binary_assignment_before_feedback.
Print Assumptions feedback_counterexample_complete.
Print Assumptions feedback_counterexample_density_normalized.
Print Assumptions recorded_bit_feedback_differs_from_true_outcome.

Definition posthoc_work_histogram {Outcome} (outcomes : list Outcome)
    (measurement : Outcome -> list Matrix) (assignment : bool -> Outcome -> R)
    (feedback : Outcome -> list Matrix) density recorded work :=
  fold_right (fun outcome total => assignment recorded outcome *
    real_part (kraus_map (feedback outcome) (kraus_map (measurement outcome) density) work work) + total) 0 outcomes.
Lemma posthoc_histogram_branch_diagonal {Outcome} (outcomes : list Outcome) measurement assignment feedback density recorded work :
  posthoc_work_histogram outcomes measurement assignment feedback density recorded work =
  real_part (true_outcome_feedback_branch outcomes measurement assignment feedback density recorded work work).
Proof.
  unfold posthoc_work_histogram, true_outcome_feedback_branch. induction outcomes; simpl; [reflexivity|].
  unfold work_matrix_add, work_matrix_scale at 1. cbn [real_part add scale]. rewrite IHoutcomes. reflexivity.
Qed.
Theorem posthoc_histogram_cannot_replace_recorded_feedback :
  real_part (recorded_feedback_branch [false;true] feedback_counterexample_measurement (binary_assignment 1 1)
    feedback_counterexample_channels feedback_counterexample_density true ket10 ket10) = 1 /\
  posthoc_work_histogram [false;true] feedback_counterexample_measurement (binary_assignment 1 1)
    feedback_counterexample_channels feedback_counterexample_density true ket10 = 0.
Proof.
  destruct recorded_bit_feedback_counterexample as [recorded true_outcome]. split.
  - rewrite recorded. reflexivity.
  - rewrite posthoc_histogram_branch_diagonal, true_outcome. reflexivity.
Qed.
Theorem recorded_feedback_register_decoder {Outcome} (outcomes : list Outcome) measurement assignment feedback density left_axis right_axis law :
  pauli_recorded_moment_law (recorded_feedback_branch outcomes measurement assignment feedback density) left_axis right_axis law ->
  joint_score law =
  pauli_expectation (recorded_feedback_branch outcomes measurement assignment feedback density false) left_axis right_axis -
  pauli_expectation (recorded_feedback_branch outcomes measurement assignment feedback density true) left_axis right_axis.
Proof. apply calibrated_signed_register_moment. Qed.
Theorem recorded_feedback_basis_word : forall recorded work spectator,
  little_endian_word recorded (first_bit work) (second_bit work) spectator =
  ((if recorded then 1 else 0) + 2 * (work_basis_number work / 2) +
    4 * (work_basis_number work mod 2) + (if spectator then 8 else 0))%nat.
Proof. intros [] [] []; reflexivity. Qed.
Print Assumptions posthoc_histogram_cannot_replace_recorded_feedback.
Print Assumptions recorded_feedback_register_decoder.
Print Assumptions recorded_feedback_basis_word.

Definition decoded_joint_score (law : bool -> bool -> bool -> bool -> R) :=
  sum_bit (fun branch => sum_bit (fun work_a => sum_bit (fun work_b => sum_bit (fun spectator =>
    law branch work_a work_b spectator * decoded_score (little_endian_word branch work_a work_b spectator))))).
Theorem decoded_joint_score_reconstruction : forall law, decoded_joint_score law = joint_score law.
Proof. intros. unfold decoded_joint_score, joint_score, sum_bit. rewrite !little_endian_score_reconstruction. reflexivity. Qed.
Definition decoded_observed_coherence (laws : Axis -> Axis -> bool -> bool -> bool -> bool -> R) :=
  complex ((decoded_joint_score (laws PauliX PauliX) + decoded_joint_score (laws PauliY PauliY))/4)
    ((decoded_joint_score (laws PauliX PauliY) - decoded_joint_score (laws PauliY PauliX))/4).
Theorem decoded_observed_coherence_reconstruction : forall laws,
  decoded_observed_coherence laws = observed_coherence laws.
Proof. intros. unfold decoded_observed_coherence, observed_coherence. rewrite !decoded_joint_score_reconstruction. reflexivity. Qed.
Theorem finite_recorded_decoded_born_score : forall branch_zero branch_one left_axis right_axis,
  decoded_joint_score (recorded_born_law branch_zero branch_one left_axis right_axis) =
  pauli_expectation (matrix_difference branch_zero branch_one) left_axis right_axis.
Proof. intros. rewrite decoded_joint_score_reconstruction. apply finite_recorded_born_score. Qed.
Theorem finite_recorded_born_observed_coherence : forall branch_zero branch_one,
  hermitian branch_zero -> hermitian branch_one ->
  observed_coherence (recorded_born_law branch_zero branch_one) =
  subtract (branch_zero ket01 ket10) (branch_one ket01 ket10).
Proof.
  intros branch_zero branch_one zero_symmetry one_symmetry.
  unfold observed_coherence. rewrite !finite_recorded_born_score.
  change (reconstructed_coherence (matrix_difference branch_zero branch_one) = subtract (branch_zero ket01 ket10) (branch_one ket01 ket10)).
  rewrite pauli_odd_entry; [reflexivity|apply difference_hermitian; assumption].
Qed.
Definition recorded_feedback_born_law {Outcome} outcomes measurement assignment feedback density :=
  recorded_born_law
    (@recorded_feedback_branch Outcome outcomes measurement assignment feedback density false)
    (@recorded_feedback_branch Outcome outcomes measurement assignment feedback density true).
Theorem recorded_feedback_decoded_born_score {Outcome} outcomes measurement assignment feedback density left_axis right_axis :
  decoded_joint_score (@recorded_feedback_born_law Outcome outcomes measurement assignment feedback density left_axis right_axis) =
  pauli_expectation (matrix_difference
    (recorded_feedback_branch outcomes measurement assignment feedback density false)
    (recorded_feedback_branch outcomes measurement assignment feedback density true)) left_axis right_axis.
Proof. apply finite_recorded_decoded_born_score. Qed.
Theorem recorded_feedback_decoded_observed_coherence {Outcome} outcomes measurement assignment feedback density :
  assignment_stochastic outcomes assignment -> measurement_complete outcomes measurement ->
  (forall bit, kraus_complete (feedback bit)) -> subnormalized_density density ->
  decoded_observed_coherence (@recorded_feedback_born_law Outcome outcomes measurement assignment feedback density) =
  subtract (explicit_feedback_branch outcomes measurement assignment feedback density false ket01 ket10)
    (explicit_feedback_branch outcomes measurement assignment feedback density true ket01 ket10).
Proof.
  intros stochastic complete feedback_complete [positive input_trace].
  rewrite decoded_observed_coherence_reconstruction. unfold recorded_feedback_born_law.
  rewrite finite_recorded_born_observed_coherence.
  - rewrite !recorded_feedback_branch_summation. reflexivity.
  - destruct (recorded_feedback_branch_positive outcomes measurement assignment feedback density false stochastic positive). assumption.
  - destruct (recorded_feedback_branch_positive outcomes measurement assignment feedback density true stochastic positive). assumption.
Qed.
Print Assumptions decoded_joint_score_reconstruction.
Print Assumptions finite_recorded_decoded_born_score.
Print Assumptions recorded_feedback_decoded_born_score.
Print Assumptions recorded_feedback_decoded_observed_coherence.
