(** Acceleration equations use column vectors. Algebraic coefficient identities
    apply to a Taylor expansion only after its analytic hypotheses are proved. *)
From Stdlib Require Import Reals Lra Field.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions StdlibRealFieldAdapter.
Import ssreflect ssrbool matrix.
Import -(coercions) rings_modules_and_algebras divalg.
Import divalg GRing.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.

Section LinearAcceleration.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Variables equations coordinates : nat.
Variable derivative : matrix.matrix scalar equations coordinates.
Variable target : matrix.matrix scalar equations 1.

Theorem separating_covector_obstructs_acceleration
 (separator : matrix.matrix scalar 1 equations) :
 separator *m derivative = 0 -> separator *m target <> 0 ->
 forall acceleration, derivative *m acceleration <> target.
Proof.
 intros annihilates separates acceleration compatible.
 apply separates. rw -compatible mulmxA annihilates mul0mx. reflexivity.
Qed.

Theorem compatible_accelerations_are_affine
 (particular acceleration : matrix.matrix scalar coordinates 1) :
 derivative *m particular = target ->
 (derivative *m acceleration = target <->
 exists homogeneous, derivative *m homogeneous = 0 /\
 acceleration = particular + homogeneous).
Proof.
 intro particular_solution; split.
 - intro solution. exists (acceleration - particular); split.
   + rw mulmxBr solution particular_solution subrr. reflexivity.
   + rw addrC subrK. reflexivity.
 - intros [homogeneous [residual ->]].
   rw mulmxDr particular_solution residual addr0. reflexivity.
Qed.

Theorem radial_correction_preserves_acceleration
 (center acceleration : matrix.matrix scalar coordinates 1) coefficient :
 derivative *m center = 0 ->
 derivative *m (acceleration + coefficient *: center) = derivative *m acceleration.
Proof. intro radial. rw mulmxDr -scalemxAr radial scaler0 addr0. reflexivity. Qed.

Theorem radial_correction_preserves_transverse_obstruction
 (separator : matrix.matrix scalar 1 equations)
 (center acceleration : matrix.matrix scalar coordinates 1) coefficient :
 separator *m derivative = 0 -> separator *m target <> 0 ->
 derivative *m (acceleration + coefficient *: center) <> target.
Proof.
 intros annihilates separates compatible.
 apply separates. rw -compatible mulmxA annihilates mul0mx. reflexivity.
Qed.
End LinearAcceleration.

Definition real_column_pairing coordinates
 (first second : matrix.matrix R coordinates 1) : R :=
 (trmx first *m second) (@fintype.ord0 0) (@fintype.ord0 0).

Lemma real_column_pairing_add coordinates
 (first second third : matrix.matrix R coordinates 1) :
 real_column_pairing first (second + third) =
 (real_column_pairing first second + real_column_pairing first third)%R.
Proof. unfold real_column_pairing. rw mulmxDr mxE. reflexivity. Qed.

Lemma real_column_pairing_scale coordinates coefficient
 (first second : matrix.matrix R coordinates 1) :
 real_column_pairing first (coefficient *: second) =
 (coefficient * real_column_pairing first second)%R.
Proof. unfold real_column_pairing. rw -scalemxAr mxE. reflexivity. Qed.

Definition norm_acceleration_residual coordinates
 (center velocity acceleration : matrix.matrix R coordinates 1) : R :=
 (real_column_pairing center acceleration + real_column_pairing velocity velocity)%R.

Definition norm_radial_coefficient coordinates
 (center velocity acceleration : matrix.matrix R coordinates 1) : R :=
 (- norm_acceleration_residual center velocity acceleration /
   real_column_pairing center center)%R.

Theorem radial_correction_solves_norm_equation coordinates
 (center velocity acceleration : matrix.matrix R coordinates 1) :
 real_column_pairing center center <> 0%R ->
 norm_acceleration_residual center velocity
   (acceleration + norm_radial_coefficient center velocity acceleration *: center) = 0%R.
Proof.
 intro nonzero. unfold norm_acceleration_residual.
 rw real_column_pairing_add real_column_pairing_scale.
 unfold norm_radial_coefficient, norm_acceleration_residual.
 field; exact nonzero.
Qed.

Theorem radial_correction_solves_both_equations equations coordinates
 (derivative : matrix.matrix R equations coordinates)
 (target : matrix.matrix R equations 1)
 (center velocity acceleration : matrix.matrix R coordinates 1) :
 derivative *m center = 0 -> derivative *m acceleration = target ->
 real_column_pairing center center <> 0%R ->
 let corrected := acceleration + norm_radial_coefficient center velocity acceleration *: center in
 derivative *m corrected = target /\
 norm_acceleration_residual center velocity corrected = 0%R.
Proof.
 intros radial compatible nonzero; cbn; split.
 - rw radial_correction_preserves_acceleration; assumption.
 - apply radial_correction_solves_norm_equation. exact nonzero.
Qed.

Print Assumptions separating_covector_obstructs_acceleration.
Print Assumptions compatible_accelerations_are_affine.
Print Assumptions radial_correction_preserves_acceleration.
Print Assumptions radial_correction_preserves_transverse_obstruction.
Print Assumptions radial_correction_solves_norm_equation.
Print Assumptions radial_correction_solves_both_equations.
