From Stdlib Require Import Reals Lra.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import StdlibRealFieldAdapter.
From OpenGororobaCheckpoint Require Import SchurAccelerationObstruction.
Import ssreflect ssrbool matrix.
Import -(coercions) rings_modules_and_algebras divalg.
Import divalg GRing.Theory.
Local Open Scope ring_scope.

Lemma real_pairing_scalar (first second : R) :
 real_column_pairing (first%:M : matrix.matrix R 1 1) second%:M = (first * second)%R.
Proof.
 unfold real_column_pairing. rw tr_scalar_mx mul_scalar_mx !mxE.
 simpl. reflexivity.
Qed.

Example nonzero_transverse_target_is_impossible :
 forall acceleration : matrix.matrix R 1 1,
 (0 : matrix.matrix R 1 1) *m acceleration <> 1%:M.
Proof.
 intro acceleration; rw mul0mx. intro impossible.
 apply (f_equal (fun value : matrix.matrix R 1 1 => value (@fintype.ord0 0) (@fintype.ord0 0))) in impossible.
 rw !mxE in impossible. change (0%R = 1%R) in impossible. lra.
Qed.

Example zero_center_cannot_repair_norm :
 forall coefficient : R,
 norm_acceleration_residual (0%:M : matrix.matrix R 1 1) 1%:M (coefficient%:M) = 1%R.
Proof.
 intro coefficient. unfold norm_acceleration_residual.
 rw !real_pairing_scalar. change (0 * coefficient + 1 * 1 = 1)%R. ring.
Qed.

Example wrong_radial_sign_doubles_norm_error :
 norm_acceleration_residual (1%:M : matrix.matrix R 1 1) 1%:M 1%:M = 2%R.
Proof. unfold norm_acceleration_residual. rw !real_pairing_scalar.
 change (1 * 1 + 1 * 1 = 2)%R. ring. Qed.

Example correct_radial_sign_cancels_norm_error :
 norm_acceleration_residual (1%:M : matrix.matrix R 1 1) 1%:M ((-1)%:M) = 0%R.
Proof. unfold norm_acceleration_residual. rw !real_pairing_scalar.
 change (1 * (-1) + 1 * 1 = 0)%R. ring. Qed.

Example radial_derivative_condition_is_essential :
 (1%:M : matrix.matrix R 1 1) *m ((0 : matrix.matrix R 1 1) + (1%R) *: (1%:M : matrix.matrix R 1 1)) <>
 (1%:M : matrix.matrix R 1 1) *m (0 : matrix.matrix R 1 1).
Proof.
 rw add0r scale1r mul1mx mulmx0. intro impossible.
 apply (f_equal (fun value : matrix.matrix R 1 1 => value (@fintype.ord0 0) (@fintype.ord0 0))) in impossible.
 rw !mxE in impossible. change (1%R = 0%R) in impossible. lra.
Qed.
