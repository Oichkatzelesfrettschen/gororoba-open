(** Pure tower operands identify right kernels by conjugating left kernels. *)
From Stdlib Require Import Reals.
From OpenGororoba Require Import RecursiveCDTower.
Lemma tower_neg_eq_zero order value :
 tower_neg order value = tower_zero order <-> value = tower_zero order.
Proof.
 split; intro equal.
 - apply (f_equal (tower_neg order)) in equal.
   rewrite tower_neg_involution, tower_neg_zero in equal. exact equal.
 - rewrite equal, tower_neg_zero. reflexivity.
Qed.
Lemma tower_conj_eq_zero order value :
 tower_conj order value = tower_zero order <-> value = tower_zero order.
Proof.
 split; intro equal.
 - apply (f_equal (tower_conj order)) in equal.
   rewrite tower_conj_involution, tower_conj_zero in equal. exact equal.
 - rewrite equal, tower_conj_zero. reflexivity.
Qed.
Theorem pure_right_left_conjugacy order operand :
 tower_pure order operand -> forall vector,
 tower_mul order vector operand = tower_neg order
   (tower_conj order (tower_mul order operand (tower_conj order vector))).
Proof.
 intros pure vector.
 rewrite tower_conj_antimorphism, tower_conj_involution,
   (tower_pure_conj_neg order operand pure), tower_mul_neg_right, tower_neg_involution.
 reflexivity.
Qed.
Theorem pure_right_left_kernel order operand :
 tower_pure order operand -> forall vector,
 tower_mul order vector operand = tower_zero order <->
 tower_mul order operand (tower_conj order vector) = tower_zero order.
Proof.
 intros pure vector. rewrite (pure_right_left_conjugacy order operand pure vector).
 rewrite tower_neg_eq_zero, tower_conj_eq_zero. reflexivity.
Qed.
Lemma tower_add_zero_right order value : tower_add order value (tower_zero order) = value.
Proof. rewrite tower_add_comm, tower_add_zero. reflexivity. Qed.
Theorem zero_upper_half_product order operand first second :
 tower_mul (S order) (operand,tower_zero order) (first,second) =
 (tower_mul order operand first,tower_mul order second operand).
Proof.
 simpl; unfold tower_sub. rewrite tower_mul_zero_right, tower_mul_zero_left,
 tower_neg_zero, tower_add_zero_right, tower_add_zero_right. reflexivity.
Qed.
Theorem pure_doubling_kernel_decomposition order operand first second :
 tower_pure order operand ->
 (tower_mul (S order) (operand,tower_zero order) (first,second) = tower_zero (S order) <->
 tower_mul order operand first = tower_zero order /\
 tower_mul order operand (tower_conj order second) = tower_zero order).
Proof.
 intro pure. rewrite zero_upper_half_product. simpl.
 split.
 - intro equal. pose proof (f_equal fst equal) as first_equal.
   pose proof (f_equal snd equal) as second_equal. simpl in first_equal, second_equal.
   split; [exact first_equal|].
   apply (proj1 (pure_right_left_kernel order operand pure second)). exact second_equal.
 - intros [first_zero second_zero].
   apply (proj2 (pure_right_left_kernel order operand pure second)) in second_zero.
   rewrite first_zero, second_zero. reflexivity.
Qed.
Definition pure_kernel_pair_transport order (pair : cd_tower order * cd_tower order) :=
 (fst pair,tower_conj order (snd pair)).
Theorem pure_kernel_pair_transport_involution order pair :
 pure_kernel_pair_transport order (pure_kernel_pair_transport order pair) = pair.
Proof. destruct pair; unfold pure_kernel_pair_transport; simpl. rewrite tower_conj_involution. reflexivity. Qed.
Theorem pure_kernel_pair_transport_membership order operand (pair : cd_tower order * cd_tower order) :
 tower_pure order operand ->
 (tower_mul (S order) (operand,tower_zero order) (pure_kernel_pair_transport order pair) = tower_zero (S order) <->
 tower_mul order operand (fst pair) = tower_zero order /\
 tower_mul order operand (snd pair) = tower_zero order).
Proof.
 intro pure. destruct pair as [first second].
 change (tower_mul (S order) (operand,tower_zero order) (first,tower_conj order second) = tower_zero (S order) <->
 tower_mul order operand first = tower_zero order /\ tower_mul order operand second = tower_zero order).
 rewrite (pure_doubling_kernel_decomposition order operand _ _ pure), tower_conj_involution.
 reflexivity.
Qed.
Print Assumptions pure_right_left_conjugacy.
Print Assumptions pure_doubling_kernel_decomposition.
Print Assumptions pure_kernel_pair_transport_membership.
From OpenGororoba Require Import StdlibRealFieldAdapter CDTowerMatrixAdapter FiniteMatrixConventions.
From Stdlib Require Import Lia.
From mathcomp Require boot order algebra.
Import ssreflect ssrbool divalg matrix mxalgebra.
Theorem pure_operator_conjugacy order operand :
 tower_pure order operand ->
 tower_right_matrix order operand = nmodule.Algebra.opp
 (matrix.mulmx (matrix.mulmx (tower_conjugation_matrix order) (tower_left_matrix order operand)) (tower_conjugation_matrix order)).
Proof.
 intro pure. apply tower_matrix_extensionality. intro vector.
 pose proof (f_equal (tower_column order) (pure_right_left_conjugacy order operand pure vector)) as correspondence.
 rw tower_column_neg tower_column_conjugation
 (proj1 (tower_multiplication_matrices order) operand (tower_conj order vector))
 tower_column_conjugation
 (proj2 (tower_multiplication_matrices order) vector operand) in correspondence.
 rw mulNmx -!mulmxA. exact correspondence.
Qed.
Theorem pure_right_left_rank order operand :
 tower_pure order operand -> mxrank (tower_right_matrix order operand) = mxrank (tower_left_matrix order operand).
Proof.
 intro pure. rw (pure_operator_conjugacy order operand pure) mxrank_opp.
 apply (@inverse_coordinate_rank stdlib_real_field _ _ _ _ (tower_left_matrix order operand)
   (matrix.mulmx (matrix.mulmx (tower_conjugation_matrix order) (tower_left_matrix order operand)) (tower_conjugation_matrix order))
   (tower_conjugation_matrix order) (tower_conjugation_matrix order)
   (tower_conjugation_matrix order) (tower_conjugation_matrix order)).
 - reflexivity.
 - rw !mulmxA tower_conjugation_matrix_involution mul1mx
     -mulmxA tower_conjugation_matrix_involution mulmx1. reflexivity.
Qed.
Theorem zero_upper_half_matrix order operand :
 tower_left_matrix (S order) (operand,tower_zero order) =
 matrix.block_mx (tower_left_matrix order operand) nmodule.Algebra.zero nmodule.Algebra.zero (tower_right_matrix order operand).
Proof.
 cbn [tower_left_matrix fst snd].
 rw (proj1 (tower_zero_multiplication_matrices order))
    (proj2 (tower_zero_multiplication_matrices order)) mul0mx nmodule.Algebra.oppr0.
 reflexivity.
Qed.
Theorem pure_doubling_rank order operand :
 tower_pure order operand ->
 mxrank (tower_left_matrix (S order) (operand,tower_zero order)) =
 ssrnat.addn (mxrank (tower_left_matrix order operand)) (mxrank (tower_left_matrix order operand)).
Proof.
 intro pure. rw zero_upper_half_matrix rank_diag_block_mx (pure_right_left_rank order operand pure). reflexivity.
Qed.
Definition tower_left_nullity order operand :=
 ssrnat.subn (tower_dimension order) (mxrank (tower_left_matrix order operand)).
Theorem pure_doubling_nullity order operand :
 tower_pure order operand ->
 tower_left_nullity (S order) (operand,tower_zero order) =
 ssrnat.addn (tower_left_nullity order operand) (tower_left_nullity order operand).
Proof.
 intro pure. unfold tower_left_nullity.
 rw (pure_doubling_rank order operand pure). cbn [tower_dimension].
 unfold ssrnat.subn, ssrnat.addn. lia.
Qed.
Print Assumptions pure_operator_conjugacy.
Print Assumptions pure_doubling_rank.
Print Assumptions pure_doubling_nullity.
From OpenGororoba Require Import ExactRankCertificate.
Local Open Scope ring_scope.
Definition doubled_kernel_frame order width
 (frame : matrix.matrix R (tower_dimension order) width) :=
 matrix.block_mx frame nmodule.Algebra.zero nmodule.Algebra.zero
 (matrix.mulmx (tower_conjugation_matrix order) frame).
Lemma conjugated_kernel_frame_residual order operand width
 (frame : matrix.matrix R (tower_dimension order) width) :
 tower_pure order operand ->
 matrix.mulmx (tower_left_matrix order operand) frame = nmodule.Algebra.zero ->
 matrix.mulmx (tower_right_matrix order operand) (matrix.mulmx (tower_conjugation_matrix order) frame) = nmodule.Algebra.zero.
Proof.
 intros pure residual.
 rw (pure_operator_conjugacy order operand pure) !mulNmx !mulmxA.
 rw -[matrix.mulmx (matrix.mulmx (tower_conjugation_matrix order) (tower_left_matrix order operand)) (tower_conjugation_matrix order) *m tower_conjugation_matrix order]mulmxA
   tower_conjugation_matrix_involution mulmx1 -mulmxA residual mulmx0 nmodule.Algebra.oppr0.
 reflexivity.
Qed.
Theorem doubled_kernel_frame_residual order operand width
 (frame : matrix.matrix R (tower_dimension order) width) :
 tower_pure order operand ->
 matrix.mulmx (tower_left_matrix order operand) frame = nmodule.Algebra.zero ->
 matrix.mulmx (tower_left_matrix (S order) (operand,tower_zero order)) (doubled_kernel_frame order width frame) = nmodule.Algebra.zero.
Proof.
 intros pure residual. unfold doubled_kernel_frame.
 rw zero_upper_half_matrix mulmx_block ?mul0mx ?mulmx0 ?nmodule.Algebra.add0r ?nmodule.Algebra.addr0
 residual (conjugated_kernel_frame_residual order operand width frame pure residual) block_mx0.
 reflexivity.
Qed.
Lemma conjugated_frame_rank order width (frame : matrix.matrix R (tower_dimension order) width) :
 mxrank (matrix.mulmx (tower_conjugation_matrix order) frame) = mxrank frame.
Proof.
 apply (@inverse_coordinate_rank stdlib_real_field _ _ _ _ frame
   (matrix.mulmx (tower_conjugation_matrix order) frame)
   (tower_conjugation_matrix order) (matrix.scalar_mx R1)
   (tower_conjugation_matrix order) (matrix.scalar_mx R1)).
 - rw mulmx1. reflexivity.
 - rw mulmx1 mulmxA tower_conjugation_matrix_involution mul1mx. reflexivity.
Qed.
Theorem doubled_kernel_frame_rank order width (frame : matrix.matrix R (tower_dimension order) width) :
 mxrank frame = width -> mxrank (doubled_kernel_frame order width frame) = ssrnat.addn width width.
Proof.
 intro independent. unfold doubled_kernel_frame.
 rw rank_diag_block_mx conjugated_frame_rank independent. reflexivity.
Qed.
Theorem doubled_kernel_frame_complete order operand width
 (frame : matrix.matrix R (tower_dimension order) width) :
 tower_pure order operand ->
 matrix.mulmx (tower_left_matrix order operand) frame = nmodule.Algebra.zero ->
 mxrank frame = width -> width = tower_left_nullity order operand ->
 forall vector : matrix.matrix R (tower_dimension (S order)) 1,
 matrix.mulmx (tower_left_matrix (S order) (operand,tower_zero order)) vector = nmodule.Algebra.zero ->
 exists coefficients : matrix.matrix R (ssrnat.addn width width) 1,
 vector = matrix.mulmx (doubled_kernel_frame order width frame) coefficients.
Proof.
 intros pure residual independent dimension.
 apply (@full_dimension_column_kernel stdlib_real_field _ _ _
   (tower_left_matrix (S order) (operand,tower_zero order)) (doubled_kernel_frame order width frame)).
 - exact (doubled_kernel_frame_residual order operand width frame pure residual).
 - change (mxrank (doubled_kernel_frame order width frame) = tower_left_nullity (S order) (operand,tower_zero order)).
   rw (pure_doubling_nullity order operand pure) (doubled_kernel_frame_rank order width frame independent).
   exact (f_equal2 ssrnat.addn dimension dimension).
Qed.
Print Assumptions doubled_kernel_frame_complete.
