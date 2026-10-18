(** Schur elimination acts on column kernels on an explicit pivot domain. *)
From Stdlib Require Import Arith.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions.
Import ssreflect ssrbool matrix mxalgebra.
Import -(coercions) rings_modules_and_algebras divalg.
Import divalg.
Import GRing.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Section SchurTransport.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Variables pivot_size residual_size : nat.
Variables (pivot pivot_inverse : matrix.matrix scalar pivot_size pivot_size)
 (upper : matrix.matrix scalar pivot_size residual_size)
 (lower : matrix.matrix scalar residual_size pivot_size)
 (trailing : matrix.matrix scalar residual_size residual_size).
Definition schur_complement := trailing - lower *m pivot_inverse *m upper.
Definition schur_left_elimination :=
 block_mx 1%:M 0 (- (lower *m pivot_inverse)) 1%:M.
Definition schur_right_elimination :=
 block_mx 1%:M (- (pivot_inverse *m upper)) 0 1%:M.
Theorem schur_block_elimination :
 pivot_inverse *m pivot = 1%:M -> pivot *m pivot_inverse = 1%:M ->
 schur_left_elimination *m (block_mx pivot upper lower trailing) *m schur_right_elimination =
 block_mx pivot 0 0 schur_complement.
Proof.
 intros inverse_left inverse_right.
 unfold schur_left_elimination, schur_right_elimination, schur_complement.
 rw !mulmx_block ?mul0mx ?mulmx0 ?mul1mx ?mulmx1 ?add0r ?addr0.
 rw ?mulNmx ?mulmxN ?mulmxA ?inverse_left ?inverse_right ?mulmx1 ?mul1mx.
 rw -[lower *m pivot_inverse *m pivot]mulmxA inverse_left mulmx1 ?subrr ?addNr ?mul0mx ?oppr0 ?add0r ?addr0.
 rw addrC. reflexivity.
Qed.
Definition schur_left_reconstruction :=
 block_mx 1%:M 0 (lower *m pivot_inverse) 1%:M.
Definition schur_right_reconstruction :=
 block_mx 1%:M (pivot_inverse *m upper) 0 1%:M.
Lemma schur_left_inverse : schur_left_reconstruction *m schur_left_elimination = 1%:M.
Proof.
 unfold schur_left_reconstruction, schur_left_elimination.
 rw mulmx_block ?mul0mx ?mulmx0 ?mul1mx ?mulmx1 ?add0r ?addr0 ?addrN.
 rw -scalar_mx_block. reflexivity.
Qed.
Lemma schur_right_inverse : schur_right_elimination *m schur_right_reconstruction = 1%:M.
Proof.
 unfold schur_right_reconstruction, schur_right_elimination.
 rw mulmx_block ?mul0mx ?mulmx0 ?mul1mx ?mulmx1 ?add0r ?addr0 ?addNr ?addrN.
 rw -scalar_mx_block. reflexivity.
Qed.
Theorem schur_block_reconstruction :
 pivot_inverse *m pivot = 1%:M -> pivot *m pivot_inverse = 1%:M ->
 block_mx pivot upper lower trailing =
 schur_left_reconstruction *m (block_mx pivot 0 0 schur_complement) *m schur_right_reconstruction.
Proof.
 intros inverse_left inverse_right.
 pose proof (schur_block_elimination inverse_left inverse_right) as eliminated.
 apply (f_equal (fun value => schur_left_reconstruction *m value *m schur_right_reconstruction)) in eliminated.
 rw !mulmxA schur_left_inverse mul1mx -mulmxA schur_right_inverse mulmx1 in eliminated.
 exact eliminated.
Qed.
Theorem schur_rank_decomposition :
 pivot_inverse *m pivot = 1%:M -> pivot *m pivot_inverse = 1%:M ->
 mxrank (block_mx pivot upper lower trailing) = (pivot_size + mxrank schur_complement)%nat.
Proof.
 intros inverse_left inverse_right.
 assert (same_rank : mxrank (block_mx pivot 0 0 schur_complement) = mxrank (block_mx pivot upper lower trailing)).
 { apply (@inverse_coordinate_rank scalar _ _ _ _
     (block_mx pivot upper lower trailing) (block_mx pivot 0 0 schur_complement)
     schur_left_elimination schur_right_elimination schur_left_reconstruction schur_right_reconstruction).
   - symmetry. exact (schur_block_elimination inverse_left inverse_right).
   - exact (schur_block_reconstruction inverse_left inverse_right). }
 rw -same_rank rank_diag_block_mx.
 assert (pivot_rank : mxrank pivot = pivot_size).
 { apply Nat.le_antisymm.
   - apply (elimT (@ssrnat.leP _ _)). exact: rank_leq_col.
   - apply (elimT (@ssrnat.leP _ _)).
     apply (@mulmx1_min_rank scalar pivot_size pivot_size pivot_size pivot pivot_inverse 1%:M).
     rw mulmx1. exact inverse_left. }
 rw pivot_rank. reflexivity.
Qed.

Theorem schur_column_kernel_coordinates
 (upper_vector : matrix.matrix scalar pivot_size 1)
 (lower_vector : matrix.matrix scalar residual_size 1) :
 pivot_inverse *m pivot = 1%:M -> pivot *m pivot_inverse = 1%:M ->
 (block_mx pivot upper lower trailing) *m
   (schur_right_elimination *m col_mx upper_vector lower_vector) = 0 <->
 upper_vector = 0 /\ schur_complement *m lower_vector = 0.
Proof.
 intros inverse_left inverse_right.
 pose proof (@coordinate_kernel_transport scalar _ _ (block_mx pivot upper lower trailing)
   schur_left_elimination schur_left_reconstruction schur_right_elimination
   (col_mx upper_vector lower_vector) schur_left_inverse) as transported.
 rw (schur_block_elimination inverse_left inverse_right) in transported.
 rw -transported.
 rw (@block_column_kernel scalar pivot_size residual_size pivot_size residual_size
   pivot schur_complement upper_vector lower_vector).
 rw (@left_inverse_reflects_zero scalar pivot_size pivot_size 1
   pivot pivot_inverse upper_vector inverse_left). reflexivity.
Qed.
Definition schur_kernel_lift (vector : matrix.matrix scalar residual_size 1) :=
 col_mx (- (pivot_inverse *m upper *m vector)) vector.
Theorem schur_kernel_lift_sound (vector : matrix.matrix scalar residual_size 1) :
 pivot_inverse *m pivot = 1%:M -> pivot *m pivot_inverse = 1%:M ->
 schur_complement *m vector = 0 ->
 block_mx pivot upper lower trailing *m schur_kernel_lift vector = 0.
Proof.
 intros inverse_left inverse_right residual.
 pose proof (proj2 (schur_column_kernel_coordinates (0 : matrix.matrix scalar pivot_size 1)
   vector inverse_left inverse_right) (conj eq_refl residual)) as lifted.
 unfold schur_right_elimination in lifted.
 rw mul_block_col ?mulmx0 ?mul1mx ?add0r ?addr0 mulNmx ?mulmxA in lifted.
 exact lifted.
Qed.
Theorem schur_kernel_lift_decode (vector : matrix.matrix scalar residual_size 1) :
 dsubmx (schur_kernel_lift vector) = vector.
Proof. unfold schur_kernel_lift. exact: col_mxKd. Qed.

Theorem schur_kernel_lift_complete
 (vector : matrix.matrix scalar (ssrnat.addn pivot_size residual_size) 1) :
 pivot_inverse *m pivot = 1%:M -> pivot *m pivot_inverse = 1%:M ->
 block_mx pivot upper lower trailing *m vector = 0 ->
 exists residual_vector, vector = schur_kernel_lift residual_vector /\
 schur_complement *m residual_vector = 0.
Proof.
 intros inverse_left inverse_right residual.
 set coordinates := schur_right_reconstruction *m vector.
 assert (round_trip : schur_right_elimination *m coordinates = vector).
 { unfold coordinates. rw mulmxA schur_right_inverse mul1mx. reflexivity. }
 pose proof (proj1 (schur_column_kernel_coordinates (usubmx coordinates)
   (dsubmx coordinates) inverse_left inverse_right)) as coordinate_kernel.
 rw vsubmxK round_trip in coordinate_kernel.
 destruct (coordinate_kernel residual) as [upper_zero lower_zero].
 exists (dsubmx coordinates). split; [|exact lower_zero].
 rw -round_trip -(vsubmxK coordinates) upper_zero.
 unfold schur_right_elimination, schur_kernel_lift.
 rw mul_block_col ?mulmx0 ?mul1mx ?add0r ?addr0 mulNmx ?col_mxKd. reflexivity.
Qed.

Theorem schur_transported_gram
 (first second : matrix.matrix scalar residual_size 1) :
 trmx (schur_kernel_lift first) *m schur_kernel_lift second =
 trmx first *m (1%:M - trmx (pivot_inverse *m upper) *m (pivot_inverse *m upper)) *m second.
Proof.
 unfold schur_kernel_lift.
 rw tr_col_mx mul_row_col !linearN /=.
 rw ?mulNmx ?mulmxN ?opprK !trmx_mul.
 rw ?mulmxDr ?mulmxDl ?mulmx1 ?mulmxA.
 rw addrC. reflexivity.
Qed.

End SchurTransport.
Print Assumptions schur_block_elimination.
Theorem skew_schur_plus_sign
 (scalar : divalg.GRing.Field.Exports.fieldType) pivot_size residual_size
 (pivot_inverse : matrix.matrix scalar pivot_size pivot_size)
 (upper : matrix.matrix scalar pivot_size residual_size)
 (trailing : matrix.matrix scalar residual_size residual_size) :
 @schur_complement scalar pivot_size residual_size pivot_inverse upper (- (trmx upper)) trailing =
 trailing + (trmx upper) *m pivot_inverse *m upper.
Proof. unfold schur_complement. rw mulNmx mulNmx opprK. reflexivity. Qed.
Print Assumptions schur_rank_decomposition.
Print Assumptions schur_column_kernel_coordinates.
Print Assumptions schur_kernel_lift_complete.
Print Assumptions skew_schur_plus_sign.
