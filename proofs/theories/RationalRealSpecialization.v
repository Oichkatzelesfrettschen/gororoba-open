From OpenGororoba Require Import StdlibRealFieldAdapter ExactRankCertificate.
From HB Require Import structures.
From Stdlib Require Import Reals Lra.
From mathcomp Require boot order algebra.
Import ssreflect ssrbool ssrfun eqtype choice.
Import -(notations, coercions) ssrint rat.
Import -(notations, coercions) nmodule.Algebra.
Import -(notations, coercions) rings_modules_and_algebras.GRing.
Import -(notations, coercions) divalg.GRing.
Lemma real_natmul_INR : forall n,
 @nmodule.Algebra.natmul _ R1 n = INR n.
Proof.
 induction n as [|n induction_equal].
 - reflexivity.
 - rw nmodule.Algebra.mulrS induction_equal.
   change (1 + INR n = INR (S n))%R. rw S_INR. ring.
Qed.
Definition real_integer (value : ssrint.int) : R := @ssrint.intmul _ R1 value.
Lemma real_integer_nonzero (value : ssrint.int) : value != ssrint.Posz 0 -> real_integer value <> 0%R.
Proof.
 intros nonzero zero_value. destruct value as [natural|natural].
 - move/eqtype.eqP: nonzero => nonzero. apply nonzero.
   unfold real_integer, ssrint.intmul in zero_value.
   rw real_natmul_INR in zero_value.
   apply f_equal. apply INR_eq. change (INR natural = INR 0). exact zero_value.
 - unfold real_integer, ssrint.intmul in zero_value.
   change (- @nmodule.Algebra.natmul _ R1 (S natural) = 0)%R in zero_value.
   rw real_natmul_INR in zero_value.
   pose proof (lt_0_INR (S natural) (Nat.lt_0_succ natural)). lra.
Qed.
Lemma real_denominator_nonzero value : real_integer (rat.denq value) <> 0%R.
Proof. apply real_integer_nonzero. exact (rat.denq_neq0 value). Qed.
Import -(coercions) rings_modules_and_algebras divalg.
Local Notation "n %:~R" := (ssrint.intmul 1 n) : ring_scope.
Local Abbreviation intr := (ssrint.intmul 1).
Import GRing.Theory.
Local Open Scope ring_scope.
Delimit Scope ring_scope with mc.
(** The embedding proofs adapt the denominator-clearing arguments from
    MathComp algebra 2.6.0 rat.v for the actual Stdlib real field. *)
Definition real_rational (value : rat) : R := ratr value.
Lemma real_rational_is_zmod_morphism : zmod_morphism real_rational.
Proof.
 have injZtoQ: @injective rat int intr by apply: intr_inj.
 have nz_den x: (denq x)%:~R != 0 :> R.
 { apply/eqP. exact (real_denominator_nonzero x). }
 move=> x y. unfold real_rational.
 apply: (canLR (mulfK (nz_den _))); apply: (mulIf (nz_den x)).
 rw mulrAC mulrBl divfK ?nz_den // mulrAC -!rmorphM.
 apply: (mulIf (nz_den y)); rw mulrAC mulrBl divfK ?nz_den //.
 rw -!(rmorphM, rmorphB); congr _%:~R; apply: injZtoQ.
 rw !(rmorphM, rmorphB) /= [_ - _]lock /= -lock !numqE.
 by rw (mulrAC y) -!mulrBl -mulrA mulrAC !mulrA.
Qed.
Lemma real_rational_is_monoid_morphism : monoid_morphism real_rational.
Proof.
 have injZtoQ: @injective rat int intr by apply: intr_inj.
 have nz_den x: (denq x)%:~R != 0 :> R.
 { apply/eqP. exact (real_denominator_nonzero x). }
 split=> [|x y]; first by unfold real_rational; rw /ratr divr1.
 unfold real_rational. rw /ratr mulrC mulrAC; apply: canLR (mulKf (nz_den _)) _; rw !mulrA.
 do 2!apply: canRL (mulfK (nz_den _)) _; rw -!rmorphM; congr _%:~R.
 apply: injZtoQ; rw !rmorphM [x * y]lock /= !numqE -lock.
 by rw -!mulrA mulrA mulrCA -!mulrA (mulrCA y).
Qed.
Lemma real_rational_zero : real_rational 0 = 0.
Proof. by rw -[0]subr0 real_rational_is_zmod_morphism subrr. Qed.
Lemma real_rational_add : {morph real_rational : x y / x + y}.
Proof.
 move=> x y; rw -[y in LHS]opprK -[- y]add0r.
 by rw !real_rational_is_zmod_morphism real_rational_zero sub0r opprK.
Qed.
Lemma real_rational_is_nmod_morphism : nmod_morphism real_rational.
Proof. exact (real_rational_zero, real_rational_add). Qed.
HB.instance Definition _ := GRing.isNmodMorphism.Build _ _ real_rational real_rational_is_nmod_morphism.
HB.instance Definition _ := GRing.isMonoidMorphism.Build _ _ real_rational real_rational_is_monoid_morphism.
Theorem actual_rational_real_rank rows columns (operator : matrix.matrix rat rows columns) :
 @mxalgebra.mxrank stdlib_real_field rows columns (matrix.map_mx real_rational operator) =
 @mxalgebra.mxrank mathcomp_rational_field rows columns operator.
Proof. exact: mxalgebra.mxrank_map. Qed.
Print Assumptions actual_rational_real_rank.
Definition integer_coordinate (value : int) : Z :=
 match value with Posz natural => Z.of_nat natural | Negz natural => Z.opp (Z.of_nat (S natural)) end.
Lemma real_integer_IZR value : real_integer value = IZR (integer_coordinate value).
Proof.
 destruct value as [natural|natural]; unfold real_integer, integer_coordinate, intmul.
 - rw real_natmul_INR. exact (INR_IZR_INZ natural).
 - change (- @nmodule.Algebra.natmul _ R1 (S natural) = IZR (- Z.of_nat (S natural)))%R.
   rw real_natmul_INR opp_IZR. f_equal. exact (INR_IZR_INZ (S natural)).
Qed.
Lemma real_rational_integer value : real_rational (ratz value) = IZR (integer_coordinate value).
Proof.
 unfold real_rational. rw ratzE ratr_int. apply real_integer_IZR.
Qed.
Lemma real_rational_fraction numerator denominator :
 real_rational (divq (ratz numerator) (ratz denominator)) =
 (IZR (integer_coordinate numerator) / IZR (integer_coordinate denominator))%R.
Proof.
 change (real_rational ((ratz numerator / ratz denominator)%mc) =
   (IZR (integer_coordinate numerator) / IZR (integer_coordinate denominator))%R).
 rw fmorph_div.
 change ((real_rational (ratz numerator) / real_rational (ratz denominator))%R =
   (IZR (integer_coordinate numerator) / IZR (integer_coordinate denominator))%R).
 rw !real_rational_integer. reflexivity.
Qed.
Print Assumptions real_rational_fraction.
Theorem rational_frame_real_complete rows columns width
 (operator : matrix.matrix rat rows columns)
 (frame : matrix.matrix rat columns width) :
 matrix.mulmx operator frame = FiniteMatrixConventions.matrix_zero mathcomp_rational_field rows width ->
 @mxalgebra.mxrank mathcomp_rational_field columns width frame =
 ssrnat.subn columns (@mxalgebra.mxrank mathcomp_rational_field rows columns operator) ->
 forall vector : matrix.matrix R columns 1,
 matrix.mulmx (matrix.map_mx real_rational operator) vector =
 FiniteMatrixConventions.matrix_zero stdlib_real_field rows 1 ->
 exists coefficients : matrix.matrix R width 1,
 vector = matrix.mulmx (matrix.map_mx real_rational frame) coefficients.
Proof.
 intros residual dimension.
 apply (@full_dimension_column_kernel stdlib_real_field rows columns width
   (matrix.map_mx real_rational operator) (matrix.map_mx real_rational frame)).
 - unfold FiniteMatrixConventions.matrix_zero in *.
   rw -matrix.map_mxM residual matrix.map_mx0. reflexivity.
 - rw !actual_rational_real_rank. exact dimension.
Qed.
Print Assumptions rational_frame_real_complete.
