(** Exact upper and lower certificates for every two-label sign matrix. *)
From Stdlib Require Import Arith List.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions.
Import ssreflect divalg matrix mxalgebra rat.
Lemma rational_sign_rank_0 : mxalgebra.mxrank (rational_sign_block false false false false) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block false false false false) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_1 : mxalgebra.mxrank (rational_sign_block true false false false) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block true false false false) (rational_sign_block true false false false) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_2 : mxalgebra.mxrank (rational_sign_block false true false false) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block false true false false) (rational_sign_block false true false false) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_3 : mxalgebra.mxrank (rational_sign_block true true false false) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block true true false false) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Negz 0))::nil)::((rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Negz 0))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_4 : mxalgebra.mxrank (rational_sign_block false false true false) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block false false true false) (rational_sign_block false false true false) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_5 : mxalgebra.mxrank (rational_sign_block true false true false) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block true false true false) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Negz 0))::nil)::((rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Negz 0))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_6 : mxalgebra.mxrank (rational_sign_block false true true false) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block false true true false) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_7 : mxalgebra.mxrank (rational_sign_block true true true false) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block true true true false) (rational_sign_block true true true false) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_8 : mxalgebra.mxrank (rational_sign_block false false false true) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block false false false true) (rational_sign_block false false false true) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_9 : mxalgebra.mxrank (rational_sign_block true false false true) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block true false false true) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Negz 0))::nil)::((rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Negz 0))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_10 : mxalgebra.mxrank (rational_sign_block false true false true) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block false true false true) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_11 : mxalgebra.mxrank (rational_sign_block true true false true) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block true true false true) (rational_sign_block true true false true) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_12 : mxalgebra.mxrank (rational_sign_block false false true true) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block false false true true) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_13 : mxalgebra.mxrank (rational_sign_block true false true true) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block true false true true) (rational_sign_block true false true true) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_14 : mxalgebra.mxrank (rational_sign_block false true true true) = 2.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 2 (rational_sign_block false true true true) (rational_sign_block false true true true) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::((rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::(rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))::nil)::nil)) (rational_literal_matrix 2 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 0))::nil)::((rat.ratz (ssrint.Posz 0))::(rat.ratz (ssrint.Posz 1))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Lemma rational_sign_rank_15 : mxalgebra.mxrank (rational_sign_block true true true true) = 1.
Proof.
  apply (@matrix_rank_witness_sound _ 2 2 1 (rational_sign_block true true true true) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Negz 0))::nil)::((rat.ratz (ssrint.Negz 0))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Posz 1))::(rat.ratz (ssrint.Posz 1))::nil)::nil)) (rational_literal_matrix 1 2 (((rat.ratz (ssrint.Negz 0))::(rat.ratz (ssrint.Posz 0))::nil)::nil)) (rational_literal_matrix 2 1 (((rat.ratz (ssrint.Posz 1))::nil)::((rat.ratz (ssrint.Posz 0))::nil)::nil))).
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
  - apply (proj1 (matrix.matrixP _ _)). intros row column.
    unfold rational_sign_block, rational_literal_matrix.
    repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
    case: row => [[|[|row]] row_bound]; case: column => [[|[|column]] column_bound]; try discriminate;
    cbn [fintype.nat_of_ord List.nth Nat.eqb rational_phase_sign]; apply (ssrbool.elimT eqtype.eqP); vm_compute; reflexivity.
Qed.
Theorem rational_sign_block_rank : forall first second third fourth,
  mxalgebra.mxrank (rational_sign_block first second third fourth) =
  if xorb (xorb first second) (xorb third fourth) then 2 else 1.
Proof. intros [] [] [] []; first [apply rational_sign_rank_0 | apply rational_sign_rank_1 | apply rational_sign_rank_2 | apply rational_sign_rank_3 | apply rational_sign_rank_4 | apply rational_sign_rank_5 | apply rational_sign_rank_6 | apply rational_sign_rank_7 | apply rational_sign_rank_8 | apply rational_sign_rank_9 | apply rational_sign_rank_10 | apply rational_sign_rank_11 | apply rational_sign_rank_12 | apply rational_sign_rank_13 | apply rational_sign_rank_14 | apply rational_sign_rank_15]. Qed.
Print Assumptions matrix_rank_witness_sound.
Print Assumptions rational_sign_block_rank.
