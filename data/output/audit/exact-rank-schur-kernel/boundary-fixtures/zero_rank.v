(** Input SHA-256: c13065eba8d9dabd299077d7698a8b119cd04aa6484236e65c26508bbe8feaa6. *)
(** Exact equations validate the proposed rational rank and complete kernel frame. *)
From Stdlib Require Import List.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions ExactRankCertificate.
Import ssreflect ssrbool divalg matrix mxalgebra rat.
Definition operator := rational_literal_matrix 2 2 ((((rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::(rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::nil))::(((rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::(rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::nil))::nil).
Definition upper_left := rational_literal_matrix 2 0 (((nil))::((nil))::nil).
Definition upper_right := rational_literal_matrix 0 2 (nil).
Definition lower_left := rational_literal_matrix 0 2 (nil).
Definition lower_right := rational_literal_matrix 2 0 (((nil))::((nil))::nil).
Definition kernel := rational_literal_matrix 2 2 ((((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 1)))::(rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::nil))::(((rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 1)))::nil))::nil).
Definition kernel_left_inverse := rational_literal_matrix 2 2 ((((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 1)))::(rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::nil))::(((rat.divq (rat.ratz (ssrint.Posz 0)) (rat.ratz (ssrint.Posz 1)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 1)))::nil))::nil).
Example retained_rank_equations : rank_certificate_check rat.rat_rat__canonical__GRing_Field operator upper_left upper_right lower_left lower_right = true.
Proof. unfold rank_certificate_check. apply Bool.andb_true_iff. split.
- apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
unfold operator, upper_left, upper_right, lower_left, lower_right, kernel, kernel_left_inverse, rational_literal_matrix, matrix_zero.
repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
cbn [fintype.nat_of_ord List.nth]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
- apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
destruct row as [row bound]; discriminate.
Qed.
Theorem retained_exact_rank : mxalgebra.mxrank operator = 0.
Proof. exact (@rank_certificate_check_sound rat.rat_rat__canonical__GRing_Field 2 2 0 operator upper_left upper_right lower_left lower_right retained_rank_equations). Qed.
Example retained_kernel_equations : kernel_frame_check rat.rat_rat__canonical__GRing_Field 0 operator kernel kernel_left_inverse = true.
Proof. unfold kernel_frame_check. apply Bool.andb_true_iff. split.
- apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
unfold operator, upper_left, upper_right, lower_left, lower_right, kernel, kernel_left_inverse, rational_literal_matrix, matrix_zero.
repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
cbn [fintype.nat_of_ord List.nth]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
- apply Bool.andb_true_iff. split.
  + apply (ssrbool.introT eqtype.eqP). apply (proj1 (matrix.matrixP _ _)). intros row column.
unfold operator, upper_left, upper_right, lower_left, lower_right, kernel, kernel_left_inverse, rational_literal_matrix, matrix_zero.
repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
cbn [fintype.nat_of_ord List.nth]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  + reflexivity.
Qed.
Theorem retained_kernel_spans : forall vector : matrix.matrix rat.rat 2 1, matrix.mulmx operator vector = matrix_zero _ 2 1 -> exists coefficients, vector = matrix.mulmx kernel coefficients.
Proof. exact (@checked_kernel_frame_complete rat.rat_rat__canonical__GRing_Field 2 2 2 0 operator kernel kernel_left_inverse retained_exact_rank retained_kernel_equations). Qed.
Print Assumptions retained_exact_rank.
Print Assumptions retained_kernel_spans.
