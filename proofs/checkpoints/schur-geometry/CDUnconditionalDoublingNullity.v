(** Every real operand doubles the left nullity of the recursive Cayley-Dickson tower.
    A nonzero real part r makes L_a + L_conj(a) = 2r I with L_a^T = L_conj(a) (and the same for R_a),
    so x^T L_a x = r |x|^2 and L_a, R_a are invertible (nullity 0) at every order.
    A zero real part is the pure case of [pure_doubling_nullity]; the two cases give [doubling_nullity].
    Transposition and conjugation give rank R_a = rank L_a for every operand ([tower_right_left_rank]),
    so the right nullity of (a,0) doubles ([right_doubling_nullity]) and both nullities of the
    operand (0,b) double ([zero_lower_half_nullity], [zero_lower_half_right_nullity]). *)
From Stdlib Require Import Reals Arith Lia Lra.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import StdlibRealFieldAdapter RecursiveCDTower CDTowerMatrixAdapter CDPureDoublingKernel
 FiniteMatrixConventions.
Import ssreflect ssrbool divalg matrix mxalgebra.
Local Open Scope R_scope.
Theorem tower_left_matrix_neg order operand :
 tower_left_matrix order (tower_neg order operand) = nmodule.Algebra.opp (tower_left_matrix order operand).
Proof.
 apply tower_matrix_extensionality. intro vector.
 rw -(proj1 (tower_multiplication_matrices order) _ vector) mulNmx
  -(proj1 (tower_multiplication_matrices order) _ vector) tower_mul_neg_left tower_column_neg. reflexivity.
Qed.
Theorem tower_right_matrix_neg order operand :
 tower_right_matrix order (tower_neg order operand) = nmodule.Algebra.opp (tower_right_matrix order operand).
Proof.
 apply tower_matrix_extensionality. intro vector.
 rw -(proj2 (tower_multiplication_matrices order) vector _) mulNmx
  -(proj2 (tower_multiplication_matrices order) vector _) tower_mul_neg_right tower_column_neg. reflexivity.
Qed.
Theorem tower_right_matrix_conjugate order operand :
 tower_right_matrix order (tower_conj order operand) =
 matrix.mulmx (matrix.mulmx (tower_conjugation_matrix order) (tower_left_matrix order operand)) (tower_conjugation_matrix order).
Proof.
 apply tower_matrix_extensionality. intro vector.
 pose proof (f_equal (tower_column order) (tower_conj_antimorphism order operand (tower_conj order vector))) as correspondence.
 rw tower_conj_involution in correspondence.
 rw tower_column_conjugation (proj1 (tower_multiplication_matrices order) operand (tower_conj order vector))
  tower_column_conjugation (proj2 (tower_multiplication_matrices order) vector (tower_conj order operand)) in correspondence.
 rw -!mulmxA. symmetry. exact correspondence.
Qed.
Theorem tower_left_matrix_conjugate order operand :
 tower_left_matrix order (tower_conj order operand) =
 matrix.mulmx (matrix.mulmx (tower_conjugation_matrix order) (tower_right_matrix order operand)) (tower_conjugation_matrix order).
Proof.
 apply tower_matrix_extensionality. intro vector.
 pose proof (f_equal (tower_column order) (tower_conj_antimorphism order (tower_conj order vector) operand)) as correspondence.
 rw tower_conj_involution in correspondence.
 rw tower_column_conjugation (proj2 (tower_multiplication_matrices order) (tower_conj order vector) operand)
  tower_column_conjugation (proj1 (tower_multiplication_matrices order) (tower_conj order operand) vector) in correspondence.
 rw -!mulmxA. symmetry. exact correspondence.
Qed.
Lemma transpose_opp rows columns (value : matrix.matrix R rows columns) :
 matrix.trmx (nmodule.Algebra.opp value) = nmodule.Algebra.opp (matrix.trmx value).
Proof. apply (proj1 (matrixP _ _)); intros row column. rw !mxE. reflexivity. Qed.
Theorem tower_conjugation_matrix_symmetric order :
 matrix.trmx (tower_conjugation_matrix order) = tower_conjugation_matrix order.
Proof.
 induction order as [|order induction_equal].
 - simpl. apply tr_scalar_mx.
 - simpl. rw tr_block_mx induction_equal !trmx0 transpose_opp tr_scalar_mx. reflexivity.
Qed.
Lemma conjugated_left_absorbs order operand :
 matrix.mulmx (tower_conjugation_matrix order) (tower_left_matrix order (tower_conj order operand)) =
 matrix.mulmx (tower_right_matrix order operand) (tower_conjugation_matrix order).
Proof.
 rw tower_left_matrix_conjugate !mulmxA tower_conjugation_matrix_involution mul1mx. reflexivity.
Qed.
Lemma conjugated_right_absorbs order operand :
 matrix.mulmx (tower_conjugation_matrix order) (tower_right_matrix order (tower_conj order operand)) =
 matrix.mulmx (tower_left_matrix order operand) (tower_conjugation_matrix order).
Proof.
 rw tower_right_matrix_conjugate !mulmxA tower_conjugation_matrix_involution mul1mx. reflexivity.
Qed.
Theorem tower_matrix_transpose order : forall operand,
 matrix.trmx (tower_left_matrix order operand) = tower_left_matrix order (tower_conj order operand) /\
 matrix.trmx (tower_right_matrix order operand) = tower_right_matrix order (tower_conj order operand).
Proof.
 induction order as [|order induction_equal]; intro operand.
 - simpl. split; apply tr_scalar_mx.
 - destruct operand as [low high]. cbn [tower_left_matrix tower_right_matrix tower_conj fst snd].
   destruct (induction_equal low) as [low_left low_right].
   destruct (induction_equal high) as [high_left high_right].
   destruct (induction_equal (tower_conj order low)) as [conj_left conj_right].
   destruct (induction_equal (tower_conj order high)) as [conj_high_left conj_high_right].
   split.
   - rw tr_block_mx transpose_opp !trmx_mul tower_conjugation_matrix_symmetric
      low_left low_right high_left high_right
      tower_left_matrix_neg tower_right_matrix_neg !mulNmx nmodule.Algebra.opprK
      (conjugated_left_absorbs order high) (conjugated_right_absorbs order high).
     reflexivity.
   - rw tr_block_mx transpose_opp conj_high_left tower_conj_involution conj_right high_left low_right
      tower_conj_neg !tower_left_matrix_neg nmodule.Algebra.opprK. reflexivity.
Qed.
Lemma scalar_mx_sum size (first second : R) :
 nmodule.Algebra.add (matrix.scalar_mx first : matrix.matrix R size size) (matrix.scalar_mx second) =
 matrix.scalar_mx (Rplus first second).
Proof.
 apply (proj1 (matrixP _ _)); intros row column. rw !mxE.
 match goal with |- context [ssrnat.nat_of_bool ?indicator] => generalize (ssrnat.nat_of_bool indicator); intro count end.
 symmetry. exact (nmodule.Algebra.mulrnDl count first second).
Qed.
Theorem tower_matrix_symmetric_part order : forall operand,
 nmodule.Algebra.add (tower_left_matrix order operand) (tower_left_matrix order (tower_conj order operand)) =
   matrix.scalar_mx (Rplus (tower_real_part order operand) (tower_real_part order operand)) /\
 nmodule.Algebra.add (tower_right_matrix order operand) (tower_right_matrix order (tower_conj order operand)) =
   matrix.scalar_mx (Rplus (tower_real_part order operand) (tower_real_part order operand)).
Proof.
 induction order as [|order induction_equal]; intro operand.
 - simpl. split; apply scalar_mx_sum.
 - destruct operand as [low high]. destruct (induction_equal low) as [low_left low_right].
   cbn [tower_left_matrix tower_right_matrix tower_conj tower_real_part fst snd].
   split.
   - rw add_block_mx tower_left_matrix_neg tower_right_matrix_neg !mulNmx nmodule.Algebra.opprK
      nmodule.Algebra.addNr nmodule.Algebra.addrN low_left low_right.
     symmetry; exact (scalar_mx_block _ _ _).
   - assert (commuted : nmodule.Algebra.add (tower_right_matrix order (tower_conj order low)) (tower_right_matrix order low) =
       matrix.scalar_mx (Rplus (tower_real_part order low) (tower_real_part order low))).
     { rw nmodule.Algebra.addrC. exact low_right. }
     rw add_block_mx tower_conj_neg tower_conj_involution !tower_left_matrix_neg nmodule.Algebra.opprK
      nmodule.Algebra.addNr nmodule.Algebra.addrN low_right commuted.
     symmetry; exact (scalar_mx_block _ _ _).
Qed.
Lemma const_mx_sum rows columns (first second : R) :
 nmodule.Algebra.add (matrix.const_mx first : matrix.matrix R rows columns) (matrix.const_mx second) =
 matrix.const_mx (Rplus first second).
Proof. apply (proj1 (matrixP _ _)); intros row column. rw !mxE. reflexivity. Qed.
Theorem tower_column_norm order : forall value,
 matrix.mulmx (matrix.trmx (tower_column order value)) (tower_column order value) =
 matrix.const_mx (tower_norm_sq order value).
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply (proj1 (matrixP _ _)); intros row column. simpl. rw !mxE.
   repeat first [progress rw matrix.mxE | progress rw bigop.big_ord_recl | progress rw bigop.big_ord0].
   simpl. change (Rplus (Rmult value value) R0 = value * (value * 1)). ring.
 - destruct value as [low high]. simpl. rw tr_col_mx mul_row_col !induction_equal const_mx_sum. reflexivity.
Qed.
Lemma tower_norm_nonneg order : forall value, 0 <= tower_norm_sq order value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - simpl. apply pow2_ge_0.
 - destruct value as [low high]. simpl. apply Rplus_le_le_0_compat; apply induction_equal.
Qed.
Theorem tower_norm_zero order : forall value, tower_norm_sq order value = 0 -> value = tower_zero order.
Proof.
 induction order as [|order induction_equal]; intros value vanishes.
 - simpl in vanishes |- *. assert (product : value * value = 0) by (rw -vanishes; ring).
   destruct (Rmult_integral _ _ product); assumption.
 - destruct value as [low high]. simpl in vanishes |- *.
   destruct (Rplus_eq_R0 _ _ (tower_norm_nonneg order low) (tower_norm_nonneg order high) vanishes) as [low_zero high_zero].
   rw (induction_equal low low_zero) (induction_equal high high_zero). reflexivity.
Qed.
Theorem symmetric_part_injective order
 (operator companion : matrix.matrix R (tower_dimension order) (tower_dimension order)) (twice : R) value :
 nmodule.Algebra.add operator companion = matrix.scalar_mx twice ->
 matrix.trmx operator = companion -> twice <> 0 ->
 matrix.mulmx operator (tower_column order value) = nmodule.Algebra.zero -> value = tower_zero order.
Proof.
 intros sum transposed nonzero residual.
 apply tower_norm_zero.
 assert (quadratic : matrix.mulmx (matrix.trmx (tower_column order value))
   (matrix.mulmx (nmodule.Algebra.add operator companion) (tower_column order value)) = nmodule.Algebra.zero).
 { rw mulmxDl mulmxDr residual mulmx0 -transposed mulmxA -trmx_mul residual trmx0 mul0mx nmodule.Algebra.addr0.
   reflexivity. }
 rw sum mul_scalar_mx -scalemxAr tower_column_norm in quadratic.
 pose proof (f_equal (fun entry : matrix.matrix R 1 1 => entry (@fintype.ord0 0) (@fintype.ord0 0)) quadratic) as entry.
 simpl in entry. rw !mxE in entry.
 change (Rmult twice (tower_norm_sq order value) = R0) in entry.
 destruct (Rmult_integral _ _ entry) as [|zero]; [contradiction|exact zero].
Qed.
Lemma trivial_kernel_annihilated_zero size (operator : matrix.matrix R size size) (image : matrix.matrix R size size) :
 (forall vector : matrix.matrix R size 1, matrix.mulmx operator vector = nmodule.Algebra.zero -> vector = nmodule.Algebra.zero) ->
 matrix.mulmx operator image = nmodule.Algebra.zero -> image = nmodule.Algebra.zero.
Proof.
 intros trivial annihilated. apply (proj1 (matrixP _ _)); intros row column.
 assert (column_residual : matrix.mulmx operator (matrix.col column image) = nmodule.Algebra.zero).
 { rw colE mulmxA annihilated mul0mx. reflexivity. }
 pose proof (f_equal (fun entry : matrix.matrix R size 1 => entry row (@fintype.ord0 0)) (trivial _ column_residual)) as entry.
 simpl in entry. rw !mxE in entry.
 rw entry. rw mxE. reflexivity.
Qed.
Theorem trivial_kernel_full_rank size (operator : matrix.matrix R size size) :
 (forall vector : matrix.matrix R size 1, matrix.mulmx operator vector = nmodule.Algebra.zero -> vector = nmodule.Algebra.zero) ->
 mxrank operator = size.
Proof.
 intro trivial.
 set kernel := kermx (matrix.trmx operator).
 assert (annihilated : matrix.mulmx operator (matrix.trmx kernel) = nmodule.Algebra.zero).
 { pose proof (mulmx_ker (matrix.trmx operator)) as residual. fold kernel in residual.
   apply (f_equal matrix.trmx) in residual. rw trmx_mul trmxK trmx0 in residual. exact residual. }
 assert (kernel_zero : kernel = nmodule.Algebra.zero).
 { pose proof (f_equal matrix.trmx (trivial_kernel_annihilated_zero size operator _ trivial annihilated)) as transposed_zero.
   rw trmxK trmx0 in transposed_zero. exact transposed_zero. }
 pose proof (mxrank_ker (matrix.trmx operator)) as kernel_rank. fold kernel in kernel_rank.
 rw kernel_zero in kernel_rank.
 rw mxrank0 in kernel_rank.
 assert (bounded : (mxrank (matrix.trmx operator) <= size)%nat).
 { exact (ssrbool.elimT (@ssrnat.leP _ _) (rank_leq_row (matrix.trmx operator))). }
 pose proof (mxrank_tr operator) as transposed_rank. unfold ssrnat.subn in kernel_rank.
 rw -transposed_rank. apply Nat.le_antisymm; [exact bounded|].
 apply Nat.sub_0_le. symmetry. exact kernel_rank.
Qed.
Lemma tower_real_part_twice_nonzero order operand :
 tower_real_part order operand <> 0 -> Rplus (tower_real_part order operand) (tower_real_part order operand) <> 0.
Proof. intros nonzero equal. apply nonzero. lra. Qed.
Theorem nonpure_left_full_rank order operand :
 tower_real_part order operand <> 0 -> mxrank (tower_left_matrix order operand) = tower_dimension order.
Proof.
 intro nonzero. apply trivial_kernel_full_rank. intros vector residual.
 rw -(tower_column_round_trip order vector) in residual |- *.
 rw (symmetric_part_injective order (tower_left_matrix order operand)
  (tower_left_matrix order (tower_conj order operand)) _ (column_tower order vector)
  (proj1 (tower_matrix_symmetric_part order operand)) (proj1 (tower_matrix_transpose order operand))
  (tower_real_part_twice_nonzero order operand nonzero) residual) tower_column_zero.
 reflexivity.
Qed.
Theorem nonpure_right_full_rank order operand :
 tower_real_part order operand <> 0 -> mxrank (tower_right_matrix order operand) = tower_dimension order.
Proof.
 intro nonzero. apply trivial_kernel_full_rank. intros vector residual.
 rw -(tower_column_round_trip order vector) in residual |- *.
 rw (symmetric_part_injective order (tower_right_matrix order operand)
  (tower_right_matrix order (tower_conj order operand)) _ (column_tower order vector)
  (proj2 (tower_matrix_symmetric_part order operand)) (proj2 (tower_matrix_transpose order operand))
  (tower_real_part_twice_nonzero order operand nonzero) residual) tower_column_zero.
 reflexivity.
Qed.
Theorem nonpure_left_nullity_zero order operand :
 tower_real_part order operand <> 0 -> tower_left_nullity order operand = 0%nat.
Proof.
 intro nonzero. unfold tower_left_nullity. rw (nonpure_left_full_rank order operand nonzero).
 apply Nat.sub_diag.
Qed.
Theorem doubling_nullity order operand :
 tower_left_nullity (S order) (operand,tower_zero order) =
 ssrnat.addn (tower_left_nullity order operand) (tower_left_nullity order operand).
Proof.
 destruct (Req_EM_T (tower_real_part order operand) 0) as [vanishes|nonzero].
 - exact (pure_doubling_nullity order operand vanishes).
 - rw (nonpure_left_nullity_zero order operand nonzero). unfold tower_left_nullity.
   rw zero_upper_half_matrix rank_diag_block_mx (nonpure_left_full_rank order operand nonzero)
    (nonpure_right_full_rank order operand nonzero). cbn [tower_dimension].
   unfold ssrnat.subn, ssrnat.addn. lia.
Qed.
(** R_a and L_a share one rank for every operand: mxrank_tr with R_a^T = R_conj(a) gives rank R_a = rank R_conj(a),
    and R_conj(a) = C L_a C with C C = 1 gives rank R_conj(a) = rank L_a. *)
Lemma conjugation_column_rank order (operator : matrix.matrix R (tower_dimension order) (tower_dimension order)) :
 mxrank (matrix.mulmx operator (tower_conjugation_matrix order)) = mxrank operator.
Proof.
 apply (@inverse_coordinate_rank stdlib_real_field _ _ _ _ operator
   (matrix.mulmx operator (tower_conjugation_matrix order))
   (matrix.scalar_mx R1) (tower_conjugation_matrix order)
   (matrix.scalar_mx R1) (tower_conjugation_matrix order)).
 - rw mul1mx. reflexivity.
 - rw mul1mx -mulmxA tower_conjugation_matrix_involution mulmx1. reflexivity.
Qed.
Theorem tower_right_left_rank order operand :
 mxrank (tower_right_matrix order operand) = mxrank (tower_left_matrix order operand).
Proof.
 rw -(mxrank_tr (tower_right_matrix order operand)) (proj2 (tower_matrix_transpose order operand))
  tower_right_matrix_conjugate conjugation_column_rank.
 apply (@inverse_coordinate_rank stdlib_real_field _ _ _ _ (tower_left_matrix order operand)
   (matrix.mulmx (tower_conjugation_matrix order) (tower_left_matrix order operand))
   (tower_conjugation_matrix order) (matrix.scalar_mx R1)
   (tower_conjugation_matrix order) (matrix.scalar_mx R1)).
 - rw mulmx1. reflexivity.
 - rw mulmx1 mulmxA tower_conjugation_matrix_involution mul1mx. reflexivity.
Qed.
Definition tower_right_nullity order operand :=
 ssrnat.subn (tower_dimension order) (mxrank (tower_right_matrix order operand)).
Theorem tower_right_left_nullity order operand :
 tower_right_nullity order operand = tower_left_nullity order operand.
Proof. unfold tower_right_nullity, tower_left_nullity. rw tower_right_left_rank. reflexivity. Qed.
Lemma doubled_nullity_arithmetic dimension rank :
 ssrnat.subn (ssrnat.addn dimension dimension) (ssrnat.addn rank rank) =
 ssrnat.addn (ssrnat.subn dimension rank) (ssrnat.subn dimension rank).
Proof. unfold ssrnat.subn, ssrnat.addn. lia. Qed.
(** The right operator of (a,0) is block_mx R_a 0 0 R_conj(a), so its rank is rank R_a + rank R_a^T. *)
Theorem zero_upper_half_right_matrix order operand :
 tower_right_matrix (S order) (operand,tower_zero order) =
 matrix.block_mx (tower_right_matrix order operand) nmodule.Algebra.zero nmodule.Algebra.zero
  (tower_right_matrix order (tower_conj order operand)).
Proof.
 cbn [tower_right_matrix fst snd].
 rw tower_conj_zero (proj1 (tower_zero_multiplication_matrices order)) nmodule.Algebra.oppr0.
 reflexivity.
Qed.
Theorem right_doubling_nullity order operand :
 tower_right_nullity (S order) (operand,tower_zero order) =
 ssrnat.addn (tower_right_nullity order operand) (tower_right_nullity order operand).
Proof.
 unfold tower_right_nullity.
 rw zero_upper_half_right_matrix rank_diag_block_mx -(proj2 (tower_matrix_transpose order operand)) mxrank_tr.
 exact (doubled_nullity_arithmetic (tower_dimension order) _).
Qed.
(** The operand (0,b) has anti-diagonal operators: L_(0,b) = block_mx 0 (-(R_b C)) (L_b C) 0 and
    R_(0,b) = block_mx 0 (-L_conj(b)) L_b 0. The half swap S = block_mx 0 1 1 0 squares to 1 and moves
    each anti-diagonal block to the diagonal, so both nullities double exactly as for (a,0). *)
Definition half_swap_matrix size : matrix.matrix R (ssrnat.addn size size) (ssrnat.addn size size) :=
 matrix.block_mx nmodule.Algebra.zero (matrix.scalar_mx R1) (matrix.scalar_mx R1) nmodule.Algebra.zero.
Lemma half_swap_involution size :
 matrix.mulmx (half_swap_matrix size) (half_swap_matrix size) = matrix.scalar_mx R1.
Proof.
 unfold half_swap_matrix.
 rw mulmx_block !mul0mx !mulmx0 !mul1mx !nmodule.Algebra.add0r !nmodule.Algebra.addr0 -scalar_mx_block.
 reflexivity.
Qed.
Theorem anti_diagonal_rank size (upper lower : matrix.matrix R size size) :
 mxrank (matrix.block_mx nmodule.Algebra.zero upper lower nmodule.Algebra.zero) =
 ssrnat.addn (mxrank upper) (mxrank lower).
Proof.
 assert (diagonal : matrix.mulmx (matrix.block_mx nmodule.Algebra.zero upper lower nmodule.Algebra.zero)
   (half_swap_matrix size) = matrix.block_mx upper nmodule.Algebra.zero nmodule.Algebra.zero lower).
 { unfold half_swap_matrix.
   rw mulmx_block !mul0mx !mulmx0 !mulmx1 !nmodule.Algebra.add0r !nmodule.Algebra.addr0. reflexivity. }
 rw -rank_diag_block_mx -diagonal. symmetry.
 apply (@inverse_coordinate_rank stdlib_real_field _ _ _ _
   (matrix.block_mx nmodule.Algebra.zero upper lower nmodule.Algebra.zero)
   (matrix.mulmx (matrix.block_mx nmodule.Algebra.zero upper lower nmodule.Algebra.zero) (half_swap_matrix size))
   (matrix.scalar_mx R1) (half_swap_matrix size) (matrix.scalar_mx R1) (half_swap_matrix size)).
 - rw mul1mx. reflexivity.
 - rw mul1mx -mulmxA half_swap_involution mulmx1. reflexivity.
Qed.
Theorem zero_lower_half_matrix order operand :
 tower_left_matrix (S order) (tower_zero order,operand) =
 matrix.block_mx nmodule.Algebra.zero
  (nmodule.Algebra.opp (matrix.mulmx (tower_right_matrix order operand) (tower_conjugation_matrix order)))
  (matrix.mulmx (tower_left_matrix order operand) (tower_conjugation_matrix order))
  nmodule.Algebra.zero.
Proof.
 cbn [tower_left_matrix fst snd].
 rw (proj1 (tower_zero_multiplication_matrices order)) (proj2 (tower_zero_multiplication_matrices order)).
 reflexivity.
Qed.
Theorem zero_lower_half_right_matrix order operand :
 tower_right_matrix (S order) (tower_zero order,operand) =
 matrix.block_mx nmodule.Algebra.zero (nmodule.Algebra.opp (tower_left_matrix order (tower_conj order operand)))
  (tower_left_matrix order operand) nmodule.Algebra.zero.
Proof.
 cbn [tower_right_matrix fst snd].
 rw tower_conj_zero (proj2 (tower_zero_multiplication_matrices order)).
 reflexivity.
Qed.
Theorem zero_lower_half_nullity order operand :
 tower_left_nullity (S order) (tower_zero order,operand) =
 ssrnat.addn (tower_left_nullity order operand) (tower_left_nullity order operand).
Proof.
 unfold tower_left_nullity.
 rw zero_lower_half_matrix anti_diagonal_rank mxrank_opp !conjugation_column_rank tower_right_left_rank.
 exact (doubled_nullity_arithmetic (tower_dimension order) _).
Qed.
Theorem zero_lower_half_right_nullity order operand :
 tower_right_nullity (S order) (tower_zero order,operand) =
 ssrnat.addn (tower_right_nullity order operand) (tower_right_nullity order operand).
Proof.
 unfold tower_right_nullity.
 rw zero_lower_half_right_matrix anti_diagonal_rank mxrank_opp -(proj1 (tower_matrix_transpose order operand))
  mxrank_tr tower_right_left_rank.
 exact (doubled_nullity_arithmetic (tower_dimension order) _).
Qed.
Print Assumptions nonpure_left_full_rank.
Print Assumptions nonpure_right_full_rank.
Print Assumptions doubling_nullity.
Print Assumptions tower_right_left_rank.
Print Assumptions tower_right_left_nullity.
Print Assumptions right_doubling_nullity.
Print Assumptions anti_diagonal_rank.
Print Assumptions zero_lower_half_nullity.
Print Assumptions zero_lower_half_right_nullity.
Print Assumptions zero_upper_half_right_matrix.
Print Assumptions zero_lower_half_matrix.
Print Assumptions zero_lower_half_right_matrix.
