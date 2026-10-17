(** Branch-signed tomography. Work basis order: |work_a work_b>.
    Hardware bits: c0=branch, c1=work_a, c2=work_b, c3=spectator.
    Real foundations are Stdlib.Reals; physical laws remain hypotheses. *)
From Stdlib Require Import Reals Lra Psatz Bool PeanoNat List.
Open Scope R_scope.
Record Complex := complex { real_part : R; imag_part : R }.
Definition zero := complex 0 0.
Definition one := complex 1 0.
Definition imaginary := complex 0 1.
Definition add (left right : Complex) := complex
  (real_part left + real_part right) (imag_part left + imag_part right).
Definition scale (factor : R) (value : Complex) := complex
  (factor * real_part value) (factor * imag_part value).
Definition negate := scale (-1).
Definition subtract (left right : Complex) := add left (negate right).
Definition conjugate (value : Complex) := complex (real_part value) (-imag_part value).
Definition multiply (left right : Complex) := complex
  (real_part left * real_part right - imag_part left * imag_part right)
  (real_part left * imag_part right + imag_part left * real_part right).
Lemma complex_ext : forall left right,
  real_part left = real_part right -> imag_part left = imag_part right -> left = right.
Proof. intros [lr li] [rr ri]; simpl; intros; subst; reflexivity. Qed.
Inductive Basis := ket00 | ket01 | ket10 | ket11.
Definition Matrix := Basis -> Basis -> Complex.
Definition first_bit (basis : Basis) : bool :=
  match basis with ket10 | ket11 => true | _ => false end.
Definition second_bit (basis : Basis) : bool :=
  match basis with ket01 | ket11 => true | _ => false end.
Definition sum_basis (values : Basis -> Complex) :=
  add (add (values ket00) (values ket01)) (add (values ket10) (values ket11)).
Definition trace_product (density observable : Matrix) :=
  sum_basis (fun row => sum_basis (fun column =>
    multiply (density row column) (observable column row))).
Definition hermitian (density : Matrix) := forall row column,
  density row column = conjugate (density column row).
Definition quadratic_form (density : Matrix) (vector : Basis -> Complex) :=
  sum_basis (fun row => sum_basis (fun column =>
    multiply (conjugate (vector row)) (multiply (density row column) (vector column)))).
Definition positive_semidefinite (density : Matrix) := hermitian density /\
  forall vector, 0 <= real_part (quadratic_form density vector).
Definition subnormalized_density (density : Matrix) := positive_semidefinite density /\
  0 <= real_part (sum_basis (fun row => density row row)) <= 1.
Inductive Axis := PauliX | PauliY.
Definition pauli (axis : Axis) (row column : bool) : Complex :=
  if Bool.eqb row column then zero else match axis with
  | PauliX => one | PauliY => if row then imaginary else negate imaginary end.
Definition tensor_pauli (left_axis right_axis : Axis) : Matrix := fun row column =>
  multiply (pauli left_axis (first_bit row) (first_bit column))
           (pauli right_axis (second_bit row) (second_bit column)).
Definition pauli_expectation (density : Matrix) (left_axis right_axis : Axis) :=
  real_part (trace_product density (tensor_pauli left_axis right_axis)).
Definition reconstructed_coherence (density : Matrix) := complex
  ((pauli_expectation density PauliX PauliX + pauli_expectation density PauliY PauliY)/4)
  ((pauli_expectation density PauliX PauliY - pauli_expectation density PauliY PauliX)/4).
(** All 16 matrix products in each trace are expanded by the proof. *)
Theorem pauli_odd_entry : forall density,
  hermitian density -> reconstructed_coherence density = density ket01 ket10.
Proof.
  intros density symmetry.
  pose proof (f_equal real_part (symmetry ket10 ket01)) as real_symmetry.
  pose proof (f_equal imag_part (symmetry ket10 ket01)) as imag_symmetry.
  unfold conjugate in real_symmetry, imag_symmetry; simpl in *.
  apply complex_ext; unfold reconstructed_coherence, pauli_expectation,
    trace_product, sum_basis, tensor_pauli, pauli, first_bit, second_bit,
    multiply, add, negate, scale, imaginary, zero, one; simpl; nra.
Qed.
Definition matrix_difference (branch_zero branch_one : Matrix) : Matrix :=
  fun row column => subtract (branch_zero row column) (branch_one row column).
Lemma difference_hermitian : forall branch_zero branch_one,
  hermitian branch_zero -> hermitian branch_one ->
  hermitian (matrix_difference branch_zero branch_one).
Proof.
  intros branch_zero branch_one zero_symmetry one_symmetry row column.
  unfold matrix_difference. rewrite (zero_symmetry row column), (one_symmetry row column).
  apply complex_ext; unfold subtract, add, negate, scale, conjugate; simpl; ring.
Qed.
Theorem branch_signed_entry : forall branch_zero branch_one,
  subnormalized_density branch_zero -> subnormalized_density branch_one ->
  reconstructed_coherence (matrix_difference branch_zero branch_one) =
  subtract (branch_zero ket01 ket10) (branch_one ket01 ket10).
Proof.
  intros branch_zero branch_one [[zero_symmetry _] _] [[one_symmetry _] _].
  apply pauli_odd_entry. apply difference_hermitian; assumption.
Qed.
(** Classical recording deletes the inter-branch blocks. *)
Definition recorded_matrix (branch_zero branch_one : Matrix)
  (left_branch : bool) (left_work : Basis) (right_branch : bool) (right_work : Basis) :=
  if Bool.eqb left_branch right_branch then
    if left_branch then branch_one left_work right_work else branch_zero left_work right_work
  else zero.
Theorem recorded_cross_branch_zero : forall branch_zero branch_one left_work right_work,
  recorded_matrix branch_zero branch_one false left_work true right_work = zero /\
  recorded_matrix branch_zero branch_one true left_work false right_work = zero.
Proof. intros; split; reflexivity. Qed.
Definition recorded_signed_block (branch_zero branch_one : Matrix) : Matrix :=
  fun row column => subtract
    (recorded_matrix branch_zero branch_one false row false column)
    (recorded_matrix branch_zero branch_one true row true column).
Theorem recorded_signed_difference : forall branch_zero branch_one,
  recorded_signed_block branch_zero branch_one = matrix_difference branch_zero branch_one.
Proof. reflexivity. Qed.
Definition sign (bit : bool) : R := if bit then -1 else 1.
Definition signed_score (branch work_a work_b spectator : bool) :=
  sign (xorb branch (xorb work_a work_b)).
Definition little_endian_word (branch work_a work_b spectator : bool) : nat :=
  (if branch then 1 else 0) + (if work_a then 2 else 0) +
  (if work_b then 4 else 0) + (if spectator then 8 else 0).
Theorem signed_score_product : forall branch work_a work_b spectator,
  signed_score branch work_a work_b spectator = sign branch * sign work_a * sign work_b.
Proof. intros [] [] [] []; unfold signed_score, sign; simpl; ring. Qed.
Theorem score_spectator_invariant : forall branch work_a work_b spectator,
  signed_score branch work_a work_b spectator = signed_score branch work_a work_b false.
Proof. reflexivity. Qed.
Definition sum_bit (values : bool -> R) := values false + values true.
Definition joint_score (law : bool -> bool -> bool -> bool -> R) :=
  sum_bit (fun branch => sum_bit (fun work_a => sum_bit (fun work_b =>
    sum_bit (fun spectator => law branch work_a work_b spectator *
      signed_score branch work_a work_b spectator)))).
Definition marginal_score (law : bool -> bool -> bool -> bool -> R) :=
  sum_bit (fun branch => sum_bit (fun work_a => sum_bit (fun work_b =>
    (law branch work_a work_b false + law branch work_a work_b true) *
    signed_score branch work_a work_b false))).
Theorem spectator_marginal_score : forall law, joint_score law = marginal_score law.
Proof. intros; unfold joint_score, marginal_score, sum_bit, signed_score, sign; simpl; ring. Qed.
Definition SpectatorMatrix := Basis -> bool -> Basis -> bool -> Complex.
Definition trace_spectator (density : SpectatorMatrix) : Matrix := fun row column =>
  add (density row false column false) (density row true column true).
Definition lifted_expectation (density : SpectatorMatrix) (observable : Matrix) :=
  sum_basis (fun row => sum_basis (fun column =>
    add (multiply (density row false column false) (observable column row))
        (multiply (density row true column true) (observable column row)))).
Theorem spectator_partial_trace : forall density observable,
  lifted_expectation density observable = trace_product (trace_spectator density) observable.
Proof.
  intros; apply complex_ext; unfold lifted_expectation, trace_product,
    trace_spectator, sum_basis, add, multiply; simpl; ring.
Qed.
(** The same epsilon in both branches expresses symmetric, independent
    assignment error. Correlated/asymmetric errors need separate bounds. *)
Definition mix_matrix (epsilon : R) (retained flipped : Matrix) : Matrix := fun row column =>
  add (scale (1-epsilon) (retained row column)) (scale epsilon (flipped row column)).
Theorem independent_branch_flip : forall epsilon branch_zero branch_one row column,
  matrix_difference (mix_matrix epsilon branch_zero branch_one)
                    (mix_matrix epsilon branch_one branch_zero) row column =
  scale (1-2*epsilon) (matrix_difference branch_zero branch_one row column).
Proof.
  intros; apply complex_ext; unfold matrix_difference, mix_matrix, subtract, add, negate, scale; simpl; ring.
Qed.
Theorem opposite_branches_cancel : forall value,
  add value (negate value) = zero /\ subtract value (negate value) = scale 2 value.
Proof.
  intros; split; apply complex_ext; unfold add, subtract, negate, scale, zero; simpl; ring.
Qed.
(** Rz(theta)=diag(exp(-i theta/2), exp(+i theta/2)). *)
Definition z_eigenvalue (bit : bool) : R := if bit then -1 else 1.
Definition basis_angle (theta_a theta_b : R) (basis : Basis) :=
  -(theta_a*z_eigenvalue (first_bit basis) + theta_b*z_eigenvalue (second_bit basis))/2.
Definition phase (angle : R) := complex (cos angle) (sin angle).
Definition z_conjugated (theta_a theta_b : R) (density : Matrix) : Matrix := fun row column =>
  multiply (phase (basis_angle theta_a theta_b row - basis_angle theta_a theta_b column))
    (density row column).
Theorem ordered_z_rotation : forall theta_a theta_b density,
  z_conjugated theta_a theta_b density ket01 ket10 =
  multiply (phase (theta_b-theta_a)) (density ket01 ket10).
Proof.
  intros; unfold z_conjugated.
  replace (basis_angle theta_a theta_b ket01 - basis_angle theta_a theta_b ket10)
    with (theta_b-theta_a) by
    (unfold basis_angle, z_eigenvalue, first_bit, second_bit; simpl; field).
  reflexivity.
Qed.
Definition modulus_squared (value : Complex) := real_part value ^ 2 + imag_part value ^ 2.
Theorem rotation_preserves_modulus_squared : forall angle value,
  modulus_squared (multiply (phase angle) value) = modulus_squared value.
Proof.
  intros angle [real_value imag_value]. pose proof (sin2_cos2 angle).
  unfold modulus_squared, multiply, phase; unfold Rsqr in *; simpl in *; nra.
Qed.
(** L1 error radii conservatively enclose Euclidean disks. *)
Definition radius (value : Complex) := Rabs (real_part value) + Rabs (imag_part value).
Theorem radius_triangle : forall left right,
  radius (add left right) <= radius left + radius right.
Proof.
  intros; unfold radius, add; simpl.
  pose proof (Rabs_triang (real_part left) (real_part right)).
  pose proof (Rabs_triang (imag_part left) (imag_part right)); lra.
Qed.
Theorem radius_encloses_euclidean_disk : forall value bound,
  radius value <= bound -> modulus_squared value <= bound^2.
Proof.
  intros [real_value imag_value] bound hypothesis.
  unfold radius, modulus_squared in *; simpl in *.
  pose proof (Rabs_pos real_value); pose proof (Rabs_pos imag_value).
  pose proof (Rsqr_abs real_value); pose proof (Rsqr_abs imag_value).
  unfold Rsqr in *; nra.
Qed.
Theorem nuisance_radius_propagation : forall signal readout drift sampling
  readout_bound drift_bound sampling_bound,
  radius readout <= readout_bound -> radius drift <= drift_bound -> radius sampling <= sampling_bound ->
  radius (subtract (add (add (add signal readout) drift) sampling) signal) <=
  readout_bound + drift_bound + sampling_bound.
Proof.
  intros signal readout drift sampling readout_bound drift_bound sampling_bound
    readout_limit drift_limit sampling_limit.
  assert (identity : subtract (add (add (add signal readout) drift) sampling) signal =
                    add (add readout drift) sampling).
  { apply complex_ext; unfold subtract, add, negate, scale; simpl; ring. }
  rewrite identity. pose proof (radius_triangle (add readout drift) sampling).
  pose proof (radius_triangle readout drift); lra.
Qed.
Theorem cause_drift_nonidentifiability : forall angle signal,
  add (multiply (phase angle) signal) zero =
  add signal (subtract (multiply (phase angle) signal) signal).
Proof.
  intros; apply complex_ext; unfold add, subtract, negate, scale, zero; simpl; ring.
Qed.
(** Physical premises remain explicit inputs. Born-score agreement includes
    correct basis rotations, bit assignment, branch signs and measurement.
    Sampling consumers must additionally justify IID and stationarity. *)
Definition setting_constant_latent_state (states : Axis -> Axis -> Matrix) :=
  forall left_axis right_axis, states left_axis right_axis = states PauliX PauliX.
Definition born_score_model (states : Axis -> Axis -> Matrix)
  (laws : Axis -> Axis -> bool -> bool -> bool -> bool -> R) :=
  forall left_axis right_axis, joint_score (laws left_axis right_axis) =
  pauli_expectation (states left_axis right_axis) left_axis right_axis.
Definition observed_coherence (laws : Axis -> Axis -> bool -> bool -> bool -> bool -> R) :=
  complex ((joint_score (laws PauliX PauliX) + joint_score (laws PauliY PauliY))/4)
          ((joint_score (laws PauliX PauliY) - joint_score (laws PauliY PauliX))/4).
Theorem observed_signed_coherence : forall states laws,
  setting_constant_latent_state states -> born_score_model states laws ->
  hermitian (states PauliX PauliX) -> observed_coherence laws = states PauliX PauliX ket01 ket10.
Proof.
  intros states laws fixed_state measurement_model symmetry.
  unfold observed_coherence. unfold born_score_model in measurement_model.
  repeat rewrite measurement_model.
  rewrite (fixed_state PauliY PauliY), (fixed_state PauliX PauliY), (fixed_state PauliY PauliX).
  apply pauli_odd_entry; exact symmetry.
Qed.
Definition stationary_marginals (law : nat -> bool -> R) :=
  forall shot outcome, law shot outcome = law 0%nat outcome.
Definition independent_binary_pair (joint : bool -> bool -> R) (first second : bool -> R) :=
  forall first_outcome second_outcome,
  joint first_outcome second_outcome = first first_outcome * second second_outcome.
Definition readout_error_independent_of_branch_and_work
  (joint : bool -> bool -> Basis -> R) (error_law : bool -> R)
  (branch_work_law : bool -> Basis -> R) :=
  forall error branch work, joint error branch work = error_law error * branch_work_law branch work.
Definition cross_job_drift_bound (first second : Complex) (bound : R) :=
  radius (subtract second first) <= bound.
Print Assumptions pauli_odd_entry.
(** The decoder maps the unsigned integer represented by a little-endian
    four-bit register back to the three bits used in the signed score. *)
Definition decoded_score (word : nat) := signed_score
  (Nat.testbit word 0) (Nat.testbit word 1) (Nat.testbit word 2) (Nat.testbit word 3).
Theorem little_endian_score_reconstruction : forall branch work_a work_b spectator,
  decoded_score (little_endian_word branch work_a work_b spectator) =
  signed_score branch work_a work_b spectator.
Proof. intros [] [] [] []; reflexivity. Qed.
Definition identity_entry (row column : bool) := if Bool.eqb row column then one else zero.
Definition pauli_projector (axis : Axis) (outcome row column : bool) :=
  scale (/2) (add (identity_entry row column) (scale (sign outcome) (pauli axis row column))).
Definition tensor_projector (left_axis right_axis : Axis) (left_outcome right_outcome : bool) : Matrix :=
  fun row column => multiply
    (pauli_projector left_axis left_outcome (first_bit row) (first_bit column))
    (pauli_projector right_axis right_outcome (second_bit row) (second_bit column)).
Definition born_probability (density : Matrix) (left_axis right_axis : Axis)
  (left_outcome right_outcome : bool) :=
  real_part (trace_product density (tensor_projector left_axis right_axis left_outcome right_outcome)).
Theorem finite_born_pauli_score : forall density left_axis right_axis,
  sum_bit (fun left_outcome => sum_bit (fun right_outcome =>
    sign left_outcome * sign right_outcome *
    born_probability density left_axis right_axis left_outcome right_outcome)) =
  pauli_expectation density left_axis right_axis.
Proof.
  intros density left_axis right_axis.
  assert (kernel_identity : forall row column,
    add (add (tensor_projector left_axis right_axis false false row column)
             (negate (tensor_projector left_axis right_axis false true row column)))
        (add (negate (tensor_projector left_axis right_axis true false row column))
             (tensor_projector left_axis right_axis true true row column)) =
    tensor_pauli left_axis right_axis row column).
  { intros [] []; destruct left_axis, right_axis; apply complex_ext;
      unfold tensor_projector, pauli_projector, identity_entry, tensor_pauli,
      pauli, first_bit, second_bit, sign, add, multiply, negate, scale,
      zero, one, imaginary; simpl; field. }
  unfold sum_bit, born_probability, pauli_expectation, sign.
  remember (tensor_projector left_axis right_axis false false) as observable00.
  remember (tensor_projector left_axis right_axis false true) as observable01.
  remember (tensor_projector left_axis right_axis true false) as observable10.
  remember (tensor_projector left_axis right_axis true true) as observable11.
  unfold trace_product, sum_basis.
  repeat rewrite <- kernel_identity.
  unfold add, negate, scale, multiply; simpl; ring.
Qed.
Lemma pauli_difference : forall branch_zero branch_one left_axis right_axis,
  pauli_expectation (matrix_difference branch_zero branch_one) left_axis right_axis =
  pauli_expectation branch_zero left_axis right_axis -
  pauli_expectation branch_one left_axis right_axis.
Proof.
  intros; unfold pauli_expectation, matrix_difference, trace_product, sum_basis,
    subtract, add, negate, scale, multiply; simpl; ring.
Qed.
Definition recorded_born_law (branch_zero branch_one : Matrix) (left_axis right_axis : Axis)
  (branch work_a work_b spectator : bool) :=
  if spectator then 0 else born_probability (if branch then branch_one else branch_zero)
    left_axis right_axis work_a work_b.
Theorem finite_recorded_born_score : forall branch_zero branch_one left_axis right_axis,
  joint_score (recorded_born_law branch_zero branch_one left_axis right_axis) =
  pauli_expectation (matrix_difference branch_zero branch_one) left_axis right_axis.
Proof.
  intros branch_zero branch_one left_axis right_axis.
  rewrite pauli_difference.
  rewrite <- (finite_born_pauli_score branch_zero left_axis right_axis),
          <- (finite_born_pauli_score branch_one left_axis right_axis).
  unfold joint_score, recorded_born_law, sum_bit, signed_score, sign; simpl; ring.
Qed.
(** Spectator=false above is a canonical realization of the reduced law.
    spectator_marginal_score transports the result to any spectator law with
    the same branch/work marginal, including correlated spectators. *)
Theorem estimator_branch_flip_scale : forall epsilon branch_zero branch_one,
  hermitian branch_zero -> hermitian branch_one ->
  reconstructed_coherence
    (matrix_difference (mix_matrix epsilon branch_zero branch_one)
                       (mix_matrix epsilon branch_one branch_zero)) =
  scale (1-2*epsilon)
    (reconstructed_coherence (matrix_difference branch_zero branch_one)).
Proof.
  intros epsilon branch_zero branch_one zero_symmetry one_symmetry.
  assert (mixed_hermitian : hermitian
    (matrix_difference (mix_matrix epsilon branch_zero branch_one)
                       (mix_matrix epsilon branch_one branch_zero))).
  { intros row column. repeat rewrite independent_branch_flip.
    pose proof (difference_hermitian branch_zero branch_one zero_symmetry one_symmetry row column) as symmetry.
    rewrite symmetry. apply complex_ext; unfold scale, conjugate; simpl; ring. }
  rewrite (pauli_odd_entry _ mixed_hermitian).
  rewrite (pauli_odd_entry _ (difference_hermitian branch_zero branch_one zero_symmetry one_symmetry)).
  apply independent_branch_flip.
Qed.
Print Assumptions finite_born_pauli_score.
Print Assumptions finite_recorded_born_score.
Print Assumptions estimator_branch_flip_scale.
Print Assumptions radius_encloses_euclidean_disk.
Print Assumptions rotation_preserves_modulus_squared.
Print Assumptions branch_signed_entry.
Print Assumptions spectator_partial_trace.
Print Assumptions independent_branch_flip.
Print Assumptions ordered_z_rotation.
Print Assumptions nuisance_radius_propagation.
Print Assumptions observed_signed_coherence.
Theorem opposite_branch_coherence_recovery : forall value,
  add (scale (/2) value) (negate (scale (/2) value)) = zero /\
  subtract (scale (/2) value) (negate (scale (/2) value)) = value.
Proof.
  intros; split; apply complex_ext; unfold add, subtract, scale, negate, zero; simpl; field.
Qed.
Definition setting_bias (bias_xx bias_yy bias_xy bias_yx : R) :=
  complex ((bias_xx+bias_yy)/4) ((bias_xy-bias_yx)/4).
Theorem setting_bias_radius : forall bias_xx bias_yy bias_xy bias_yx,
  radius (setting_bias bias_xx bias_yy bias_xy bias_yx) <=
  (Rabs bias_xx+Rabs bias_yy+Rabs bias_xy+Rabs bias_yx)/4.
Proof.
  intros; unfold radius, setting_bias; simpl.
  unfold Rdiv. repeat rewrite Rabs_mult.
  replace (Rabs (/4)) with (/4) by
    (symmetry; apply Rabs_pos_eq; left; apply Rinv_0_lt_compat; lra).
  replace (Rabs 4) with 4 by (symmetry; apply Rabs_pos_eq; lra).
  pose proof (Rabs_triang bias_xx bias_yy).
  pose proof (Rabs_triang bias_xy (-bias_yx)) as imaginary_bound.
  rewrite Rabs_Ropp in imaginary_bound. unfold Rminus; lra.
Qed.
Fixpoint independent_binary_product (law : bool -> R) (outcomes : list bool) : R :=
  match outcomes with nil => 1 | cons outcome remaining =>
    law outcome * independent_binary_product law remaining end.
Definition iid_binary_shots (finite_joint_law : list bool -> R) (law : bool -> R) :=
  0 <= law false /\ 0 <= law true /\ law false+law true=1 /\
  forall outcomes, finite_joint_law outcomes = independent_binary_product law outcomes.
Print Assumptions opposite_branch_coherence_recovery.
Print Assumptions setting_bias_radius.
Print Assumptions little_endian_score_reconstruction.
Print Assumptions recorded_cross_branch_zero.
Print Assumptions cause_drift_nonidentifiability.
(** Equal branch weights and opposite conditional phase kicks give pure
    attenuation. Resetting the control removes that averaging premise. *)
Theorem balanced_control_zz_attenuation : forall coupling signal,
  add (scale (/2) (multiply (phase coupling) signal))
      (scale (/2) (multiply (phase (-coupling)) signal)) =
  scale (cos coupling) signal.
Proof.
  intros; apply complex_ext; unfold add, scale, multiply, phase; simpl;
    rewrite cos_neg, sin_neg; field.
Qed.
Print Assumptions balanced_control_zz_attenuation.
