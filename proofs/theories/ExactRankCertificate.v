From Stdlib Require Import Arith List.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions.
Import ssreflect ssrbool divalg matrix mxalgebra rat.
Set Implicit Arguments.
Section CertifiedRank.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Definition rank_certificate_check rows columns rank
 (operator : matrix.matrix scalar rows columns)
 (upper_left : matrix.matrix scalar rows rank)
 (upper_right : matrix.matrix scalar rank columns)
 (lower_left : matrix.matrix scalar rank rows)
 (lower_right : matrix.matrix scalar columns rank) :=
 andb (eqtype.eq_op operator (matrix.mulmx upper_left upper_right))
 (eqtype.eq_op (matrix.mulmx (matrix.mulmx lower_left operator) lower_right)
 (matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar))).
Theorem rank_certificate_check_sound rows columns rank
 (operator : matrix.matrix scalar rows columns)
 (upper_left : matrix.matrix scalar rows rank)
 (upper_right : matrix.matrix scalar rank columns)
 (lower_left : matrix.matrix scalar rank rows)
 (lower_right : matrix.matrix scalar columns rank) :
 rank_certificate_check operator upper_left upper_right lower_left lower_right = true ->
 mxalgebra.mxrank operator = rank.
Proof.
 intro accepted. apply Bool.andb_true_iff in accepted.
 destruct accepted as [upper lower].
 apply (ssrbool.elimT eqtype.eqP) in upper.
 apply (ssrbool.elimT eqtype.eqP) in lower.
 exact (@matrix_rank_witness_sound scalar rows columns rank operator upper_left upper_right lower_left lower_right upper lower).
Qed.
End CertifiedRank.
Print Assumptions rank_certificate_check_sound.
Section CompleteKernel.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Theorem full_dimension_column_kernel rows columns width
 (operator : matrix.matrix scalar rows columns)
 (frame : matrix.matrix scalar columns width) :
 matrix.mulmx operator frame = matrix_zero scalar rows width ->
 mxalgebra.mxrank frame = ssrnat.subn columns (mxalgebra.mxrank operator) ->
 forall vector : matrix.matrix scalar columns 1,
 matrix.mulmx operator vector = matrix_zero scalar rows 1 ->
 exists coefficients : matrix.matrix scalar width 1,
 vector = matrix.mulmx frame coefficients.
Proof.
 intros residual dimension vector vector_zero.
 assert (row_residual : matrix.mulmx (matrix.trmx frame) (matrix.trmx operator) = matrix_zero scalar width rows).
 { apply (f_equal matrix.trmx) in residual.
   unfold matrix_zero in *. rw matrix.trmx_mul matrix.trmx0 in residual. exact residual. }
 assert (included : mxalgebra.submx (matrix.trmx frame) (mxalgebra.kermx (matrix.trmx operator))).
 { apply (ssrbool.introT mxalgebra.sub_kermxP). exact row_residual. }
 pose proof (mxalgebra.mxrank_leqif_sup included) as rank_comparison.
 destruct rank_comparison as [_ equality].
 assert (reverse : mxalgebra.submx (mxalgebra.kermx (matrix.trmx operator)) (matrix.trmx frame)).
 { rw -equality. apply (ssrbool.introT eqtype.eqP).
   rw mxalgebra.mxrank_tr mxalgebra.mxrank_ker mxalgebra.mxrank_tr dimension. reflexivity. }
 assert (vector_included : mxalgebra.submx (matrix.trmx vector) (mxalgebra.kermx (matrix.trmx operator))).
 { apply (ssrbool.introT mxalgebra.sub_kermxP).
   apply (f_equal matrix.trmx) in vector_zero.
   unfold matrix_zero in *. rw matrix.trmx_mul matrix.trmx0 in vector_zero. exact vector_zero. }
 pose proof (mxalgebra.submx_trans vector_included reverse) as span.
 destruct (ssrbool.elimT mxalgebra.submxP span) as [coefficients factorization].
 exists (matrix.trmx coefficients).
 apply (f_equal matrix.trmx) in factorization.
 rw matrix.trmx_mul !matrix.trmxK in factorization. exact factorization.
Qed.
End CompleteKernel.
Print Assumptions full_dimension_column_kernel.
Section CompleteFrameCheck.
Variable scalar : divalg.GRing.Field.Exports.fieldType.
Definition kernel_frame_check rows columns width rank
 (operator : matrix.matrix scalar rows columns)
 (frame : matrix.matrix scalar columns width)
 (left_inverse : matrix.matrix scalar width columns) :=
 andb (eqtype.eq_op (matrix.mulmx operator frame) (matrix_zero scalar rows width))
 (andb (eqtype.eq_op (matrix.mulmx left_inverse frame)
 (matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar)))
 (Nat.eqb width (ssrnat.subn columns rank))).
Theorem checked_kernel_frame_complete rows columns width rank
 (operator : matrix.matrix scalar rows columns)
 (frame : matrix.matrix scalar columns width)
 (left_inverse : matrix.matrix scalar width columns) :
 mxalgebra.mxrank operator = rank ->
 kernel_frame_check rank operator frame left_inverse = true ->
 forall vector : matrix.matrix scalar columns 1,
 matrix.mulmx operator vector = matrix_zero scalar rows 1 ->
 exists coefficients : matrix.matrix scalar width 1,
 vector = matrix.mulmx frame coefficients.
Proof.
 intros operator_rank accepted.
 apply Bool.andb_true_iff in accepted. destruct accepted as [residual rest].
 apply Bool.andb_true_iff in rest. destruct rest as [inverse dimension].
 apply (elimT eqtype.eqP) in residual.
 apply (elimT eqtype.eqP) in inverse.
 apply Nat.eqb_eq in dimension.
 assert (frame_rank : mxalgebra.mxrank frame = width).
 { apply Nat.le_antisymm.
   - apply (elimT (@ssrnat.leP _ _)). exact: mxalgebra.rank_leq_col.
   - apply (elimT (@ssrnat.leP _ _)).
     apply (@mxalgebra.mulmx1_min_rank scalar width columns width frame left_inverse
       (matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar))).
     rw matrix.mulmx1. exact inverse. }
 apply (full_dimension_column_kernel residual).
 rw frame_rank operator_rank. exact dimension.
Qed.
Theorem left_inverse_coordinates_unique columns width
 (frame : matrix.matrix scalar columns width)
 (left_inverse : matrix.matrix scalar width columns)
 (first second : matrix.matrix scalar width 1) :
 matrix.mulmx left_inverse frame = matrix.scalar_mx (@rings_modules_and_algebras.GRing.one scalar) ->
 matrix.mulmx frame first = matrix.mulmx frame second -> first = second.
Proof.
 intros inverse equal.
 apply (f_equal (matrix.mulmx left_inverse)) in equal.
 rw !matrix.mulmxA inverse !matrix.mul1mx in equal. exact equal.
Qed.
End CompleteFrameCheck.
Print Assumptions checked_kernel_frame_complete.
Print Assumptions left_inverse_coordinates_unique.
