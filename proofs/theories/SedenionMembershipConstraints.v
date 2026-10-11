(** * Sedenion membership constraints and scalar counterexamples.

    The real polynomial criterion uses the scalar parts separately from the
    imaginary octonion norms. The zero-locus theorem below concerns that
    polynomial; the identification with singular left multiplication requires
    the sedenion determinant factorization. Equal half norms alone are weaker.
    The operator witnesses independently refute the two invalid-domain cases. *)

From Stdlib Require Import Reals Lra.
From OpenGororoba Require Import CayleyDicksonAlgebra Sedenion.
Open Scope R_scope.

Definition sedenion_d2 (scalar_left scalar_right norm_left norm_right inner : R) : R :=
  let scalar_norm := scalar_left^2 + scalar_right^2 in
  scalar_norm^2 + 2 * scalar_norm * (norm_left + norm_right) +
  (norm_left - norm_right)^2 + 4 * inner^2.

Theorem sedenion_d2_zero_iff : forall scalar_left scalar_right norm_left norm_right inner,
  0 <= norm_left -> 0 <= norm_right ->
  (sedenion_d2 scalar_left scalar_right norm_left norm_right inner = 0 <->
   scalar_left = 0 /\ scalar_right = 0 /\ norm_left = norm_right /\ inner = 0).
Proof.
  intros scalar_left scalar_right norm_left norm_right inner left_nonnegative right_nonnegative.
  unfold sedenion_d2. split.
  - intro polynomial_zero.
    pose proof (Rle_0_sqr scalar_left).
    pose proof (Rle_0_sqr scalar_right).
    pose proof (Rle_0_sqr (scalar_left^2 + scalar_right^2)).
    pose proof (Rle_0_sqr (norm_left - norm_right)).
    pose proof (Rle_0_sqr inner).
    unfold Rsqr in *.
    assert (0 <= (scalar_left^2 + scalar_right^2) * (norm_left + norm_right))
      by (apply Rmult_le_pos; nra).
    assert (scalar_left^2 + scalar_right^2 = 0) by nra.
    repeat split; nra.
  - intros [-> [-> [-> ->]]]. ring.
Qed.
Print Assumptions sedenion_d2_zero_iff.

(** These are the five partial derivatives in scalar/norm/inner-product
    coordinates. Their vanishing prevents a regular-level-set argument from
    D2 alone; use the component constraints for a Jacobian rank calculation. *)
Definition sedenion_d2_gradient (scalar_left scalar_right norm_left norm_right inner : R)
    : R * R * R * R * R :=
  let total := scalar_left^2 + scalar_right^2 + norm_left + norm_right in
  (4 * scalar_left * total, 4 * scalar_right * total,
   2 * (scalar_left^2 + scalar_right^2) + 2 * (norm_left - norm_right),
   2 * (scalar_left^2 + scalar_right^2) - 2 * (norm_left - norm_right),
   8 * inner).

Theorem sedenion_d2_gradient_vanishes : forall norm,
  sedenion_d2_gradient 0 0 norm norm 0 = (0, 0, 0, 0, 0).
Proof. intro norm. unfold sedenion_d2_gradient. repeat f_equal; ring. Qed.
Print Assumptions sedenion_d2_gradient_vanishes.

Definition membership_sed_scale (factor : R) (value : CDSed) : CDSed :=
  mkSed
    (mkOct (quat_scale factor (oct_lo (sed_lo value)))
           (quat_scale factor (oct_hi (sed_lo value))))
    (mkOct (quat_scale factor (oct_lo (sed_hi value)))
           (quat_scale factor (oct_hi (sed_hi value)))).

Definition parallel_imaginary_halves : CDSed :=
  mkSed (oct_e 1) (oct_e 1).
Definition scalar_and_imaginary_halves : CDSed :=
  mkSed (oct_e 0) (oct_e 1).
Definition scalar_and_imaginary_left_inverse : CDSed :=
  mkSed (oct_e 0) (mkOct (mkQuat 0 (-1) 0 0) quat_zero).

Ltac expand_membership_operator :=
  cbv [parallel_imaginary_halves scalar_and_imaginary_halves
       scalar_and_imaginary_left_inverse membership_sed_scale
       sed_mul sed_zero oct_mul oct_conj oct_e oct_zero
       quat_mul quat_add quat_neg quat_conj quat_scale quat_zero quat_one
       sed_lo sed_hi oct_lo oct_hi qa qb qc qd];
  f_equal; f_equal; f_equal; ring.

Theorem parallel_halves_left_square : forall value,
  sed_mul parallel_imaginary_halves (sed_mul parallel_imaginary_halves value) =
  membership_sed_scale (-2) value.
Proof.
  intros [[[a0 a1 a2 a3] [a4 a5 a6 a7]] [[a8 a9 a10 a11] [a12 a13 a14 a15]]].
  expand_membership_operator.
Qed.
Print Assumptions parallel_halves_left_square.

Theorem scalar_halves_left_inverse : forall value,
  sed_mul scalar_and_imaginary_left_inverse (sed_mul scalar_and_imaginary_halves value) =
  membership_sed_scale 2 value.
Proof.
  intros [[[a0 a1 a2 a3] [a4 a5 a6 a7]] [[a8 a9 a10 a11] [a12 a13 a14 a15]]].
  expand_membership_operator.
Qed.
Print Assumptions scalar_halves_left_inverse.

Theorem membership_scale_injective_at_zero : forall factor value,
  factor <> 0 -> membership_sed_scale factor value = sed_zero -> value = sed_zero.
Proof.
  intros factor [[[a0 a1 a2 a3] [a4 a5 a6 a7]] [[a8 a9 a10 a11] [a12 a13 a14 a15]]]
    factor_nonzero scaled_zero.
  unfold membership_sed_scale, sed_zero, oct_zero, quat_zero, quat_scale in scaled_zero.
  simpl in scaled_zero. injection scaled_zero; intros.
  unfold sed_zero, oct_zero, quat_zero. repeat f_equal; nra.
Qed.
Print Assumptions membership_scale_injective_at_zero.

Theorem parallel_halves_trivial_kernel : forall value,
  sed_mul parallel_imaginary_halves value = sed_zero -> value = sed_zero.
Proof.
  intros value kernel_member.
  pose proof (parallel_halves_left_square value) as square_identity.
  rewrite kernel_member in square_identity.
  assert (sed_mul parallel_imaginary_halves sed_zero = sed_zero) as zero_product
    by (expand_membership_operator).
  rewrite zero_product in square_identity.
  apply (membership_scale_injective_at_zero (-2) value); [lra|symmetry; exact square_identity].
Qed.
Print Assumptions parallel_halves_trivial_kernel.

Theorem scalar_halves_trivial_kernel : forall value,
  sed_mul scalar_and_imaginary_halves value = sed_zero -> value = sed_zero.
Proof.
  intros value kernel_member.
  pose proof (scalar_halves_left_inverse value) as inverse_identity.
  rewrite kernel_member in inverse_identity.
  assert (sed_mul scalar_and_imaginary_left_inverse sed_zero = sed_zero) as zero_product
    by (expand_membership_operator).
  rewrite zero_product in inverse_identity.
  apply (membership_scale_injective_at_zero 2 value); [lra|symmetry; exact inverse_identity].
Qed.
Print Assumptions scalar_halves_trivial_kernel.
