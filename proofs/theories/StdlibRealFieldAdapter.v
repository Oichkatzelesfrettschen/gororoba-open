From mathcomp Require boot order algebra.
From Stdlib Require Import Reals ClassicalEpsilon FunctionalExtensionality.
From HB Require Import structures.
Import ssreflect ssrbool ssrfun eqtype choice.
Import -(notations, coercions) nmodule.Algebra.
Import -(notations, coercions) rings_modules_and_algebras.GRing.
Import -(notations, coercions) divalg.GRing.
Definition real_eqb (x y : R) := match Req_EM_T x y with left _ => true | right _ => false end.
Lemma real_eqP : eqtype.eq_axiom real_eqb.
Proof. intros x y; unfold real_eqb; destruct (Req_EM_T x y); constructor; assumption. Qed.
HB.instance Definition _ := eqtype.hasDecEq.Build R real_eqP.
Definition real_find (predicate : R -> bool) (_ : nat) : option R :=
  let chosen := epsilon (inhabits R0) (fun x => predicate x = true) in
  if predicate chosen then Some chosen else None.
Lemma real_find_correct (predicate : R -> bool) n x :
  real_find predicate n = Some x -> predicate x.
Proof. unfold real_find; destruct (predicate _) eqn:present; intro found; inversion found; subst; exact present. Qed.
Lemma real_find_complete (predicate : R -> bool) :
  (exists x, predicate x) -> exists n, real_find predicate n.
Proof.
 intro witness. exists 0%N. unfold real_find.
 assert (present : predicate (epsilon (inhabits R0) (fun x => predicate x = true)) = true).
 { apply epsilon_spec; exact witness. }
 rw present. reflexivity.
Qed.
Lemma real_find_ext (first second : R -> bool) :
 first =1 second -> real_find first =1 real_find second.
Proof.
 intro same. assert (equal : first = second).
 { apply functional_extensionality; exact same. }
 rw equal. intro index; reflexivity.
Qed.
HB.instance Definition _ := hasChoice.Build R real_find_correct real_find_complete real_find_ext.
Lemma real_addA : associative Rplus.
Proof. intros x y z; symmetry; apply Rplus_assoc. Qed.
HB.instance Definition _ := nmodule.Algebra.isZmodule.Build R real_addA Rplus_comm Rplus_0_l Rplus_opp_l.
Lemma real_mulA : associative Rmult.
Proof. intros x y z; symmetry; apply Rmult_assoc. Qed.
Lemma real_one_nonzero : R1 != R0.
Proof. apply/eqP; exact R1_neq_R0. Qed.
HB.instance Definition _ := rings_modules_and_algebras.GRing.Zmodule_isComNzRing.Build R
 real_mulA Rmult_comm Rmult_1_l Rmult_plus_distr_r real_one_nonzero.
Lemma real_inv_l x : x != R0 -> Rmult (Rinv x) x = R1.
Proof. move=> /eqP nonzero; exact (Rinv_l x nonzero). Qed.
HB.instance Definition _ := divalg.GRing.ComNzRing_isField.Build R real_inv_l Rinv_0.
Definition stdlib_real_field : divalg.GRing.Field.type := @divalg.GRing.Field.Pack R (divalg.GRing.Field.on R).
Print Assumptions stdlib_real_field.
Definition mathcomp_rational_field : divalg.GRing.Field.type :=
  rat.rat_rat__canonical__GRing_Field.

Definition field_semiring (scalar : divalg.GRing.Field.type) :=
  divalg.GRing.Field.Exports.GRing_Field__to__GRing_PzSemiRing scalar.

(** The embedding and entrywise correspondence are explicit obligations. *)
Theorem rational_rank_specialization
  (embedding : rings_modules_and_algebras.GRing.RMorphism.type
    (field_semiring mathcomp_rational_field)
    (field_semiring stdlib_real_field))
  rows columns
  (rational_operator : matrix.matrix rat.rat rows columns)
  (real_operator : matrix.matrix R rows columns) :
  real_operator = matrix.map_mx
    (rings_modules_and_algebras.GRing.RMorphism.sort embedding)
    rational_operator ->
  @mxalgebra.mxrank stdlib_real_field rows columns real_operator =
  @mxalgebra.mxrank mathcomp_rational_field rows columns rational_operator.
Proof.
  intro correspondence. rw correspondence.
  exact (@mxalgebra.mxrank_map mathcomp_rational_field stdlib_real_field
    embedding rows columns rational_operator).
Qed.
Print Assumptions rational_rank_specialization.
