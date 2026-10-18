(** Input SHA-256: 58f0c01d23ec128487fba325eee0ae28d04bb090f9230e61361eaa15add9a8ae. *)
(** Exact equations validate the proposed rational rank and complete kernel frame. *)
From Stdlib Require Import List.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions ExactRankCertificate.
Import ssreflect ssrbool divalg matrix mxalgebra rat.
Definition operator := rational_literal_matrix 0 0 (nil).
Definition upper_left := rational_literal_matrix 0 0 (nil).
Definition upper_right := rational_literal_matrix 0 0 (nil).
Definition lower_left := rational_literal_matrix 0 0 (nil).
Definition lower_right := rational_literal_matrix 0 0 (nil).
Definition kernel := rational_literal_matrix 0 0 (nil).
Definition kernel_left_inverse := rational_literal_matrix 0 0 (nil).
Example retained_rank_equations : rank_certificate_check rat.rat_rat__canonical__GRing_Field operator upper_left upper_right lower_left lower_right = true.
Proof. unfold rank_certificate_check. apply Bool.andb_true_iff. split.
- apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
destruct row as [row bound]; discriminate.
- apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
destruct row as [row bound]; discriminate.
Qed.
Theorem retained_exact_rank : mxalgebra.mxrank operator = 0.
Proof. exact (@rank_certificate_check_sound rat.rat_rat__canonical__GRing_Field 0 0 0 operator upper_left upper_right lower_left lower_right retained_rank_equations). Qed.
Example retained_kernel_equations : kernel_frame_check rat.rat_rat__canonical__GRing_Field 0 operator kernel kernel_left_inverse = true.
Proof. unfold kernel_frame_check. apply Bool.andb_true_iff. split.
- apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
destruct row as [row bound]; discriminate.
- apply Bool.andb_true_iff. split.
  + apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
destruct row as [row bound]; discriminate.
  + reflexivity.
Qed.
Theorem retained_kernel_spans : forall vector : matrix.matrix rat.rat 0 1, matrix.mulmx operator vector = matrix_zero _ 0 1 -> exists coefficients, vector = matrix.mulmx kernel coefficients.
Proof. exact (@checked_kernel_frame_complete rat.rat_rat__canonical__GRing_Field 0 0 0 0 operator kernel kernel_left_inverse retained_exact_rank retained_kernel_equations). Qed.
Print Assumptions retained_exact_rank.
Print Assumptions retained_kernel_spans.
