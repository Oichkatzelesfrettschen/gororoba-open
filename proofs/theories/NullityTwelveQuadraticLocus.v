(** Real zero set of the eight selected-center quadratic generators.

    The coordinate equations use z5,z6,z13,z16,...,z20 of the
    e1+e18 centered Schur certificate. Thirteen other coordinates are
    free. Matrix-coefficient completeness, curve realization and tangent
    limits require separate correspondences with the multiplication model. *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Definition quadratic_common_zero
    (z5 z6 z13 z16 z17 z18 z19 z20 : R) : Prop :=
  z6^2-z16^2 = 0 /\
  z5*z6-z13*z16 = 0 /\
  z13*z6+z16*z5 = 0 /\
  z17*z5-z13*z20+z16*z17+z20*z6 = 0 /\
  z13*z19+z18*z5+z16*z18-z19*z6 = 0 /\
  z19*z5-z13*z18+z16*z19+z18*z6 = 0 /\
  z13*z17+z20*z5+z16*z20-z17*z6 = 0 /\
  z16*z6 = 0.

Definition coordinate_plane_a15
    (z6 z16 z17 z18 z19 z20 : R) : Prop :=
  z6=0 /\ z16=0 /\ z17=0 /\ z18=0 /\ z19=0 /\ z20=0.

Definition coordinate_plane_b17 (z5 z6 z13 z16 : R) : Prop :=
  z6=0 /\ z16=0 /\ z5=0 /\ z13=0.

Lemma two_squares_zero_iff : forall first second : R,
  first^2+second^2=0 <-> first=0 /\ second=0.
Proof.
  intros first second; split.
  - intro sum_zero.
    pose proof (Rle_0_sqr first).
    pose proof (Rle_0_sqr second).
    unfold Rsqr in *; split; nra.
  - intros [-> ->]; ring.
Qed.

Lemma four_squares_zero_iff : forall first second third fourth : R,
  first^2+second^2+third^2+fourth^2=0 <->
  first=0 /\ second=0 /\ third=0 /\ fourth=0.
Proof.
  intros first second third fourth; split.
  - intro sum_zero.
    pose proof (Rle_0_sqr first).
    pose proof (Rle_0_sqr second).
    pose proof (Rle_0_sqr third).
    pose proof (Rle_0_sqr fourth).
    unfold Rsqr in *; repeat split; nra.
  - intros [-> [-> [-> ->]]]; ring.
Qed.

Theorem first_obstruction_norm_identity : forall z6 z16 : R,
  (z6^2-z16^2)^2+4*(z16*z6)^2=(z6^2+z16^2)^2.
Proof. intros; ring. Qed.

Theorem residual_obstruction_norm_identity : forall z5 z13 z17 z18 z19 z20 : R,
  (z5*z17-z13*z20)^2+(z5*z18+z13*z19)^2+
  (z5*z19-z13*z18)^2+(z5*z20+z13*z17)^2 =
  (z5^2+z13^2)*(z17^2+z18^2+z19^2+z20^2).
Proof. intros; ring. Qed.

Theorem selected_quadratic_zero_set : forall z5 z6 z13 z16 z17 z18 z19 z20,
  quadratic_common_zero z5 z6 z13 z16 z17 z18 z19 z20 <->
  coordinate_plane_a15 z6 z16 z17 z18 z19 z20 \/
  coordinate_plane_b17 z5 z6 z13 z16.
Proof.
  intros z5 z6 z13 z16 z17 z18 z19 z20; split.
  - intros [first_zero [second_zero [third_zero [fourth_zero
      [fifth_zero [sixth_zero [seventh_zero eighth_zero]]]]]]].
    assert (z6_zero : z6=0).
    { destruct (Rmult_integral _ _ eighth_zero) as [z16_zero | z6_zero].
      - rewrite z16_zero in first_zero; nra.
      - exact z6_zero. }
    assert (z16_zero : z16=0) by (rewrite z6_zero in first_zero; nra).
    rewrite z6_zero, z16_zero in fourth_zero, fifth_zero, sixth_zero, seventh_zero.
    assert (product_zero : (z5^2+z13^2)*(z17^2+z18^2+z19^2+z20^2)=0).
    { rewrite <- residual_obstruction_norm_identity.
      assert (first_residual : z5*z17-z13*z20=0) by nra.
      assert (second_residual : z5*z18+z13*z19=0) by nra.
      assert (third_residual : z5*z19-z13*z18=0) by nra.
      assert (fourth_residual : z5*z20+z13*z17=0) by nra.
      rewrite first_residual, second_residual, third_residual, fourth_residual; ring. }
    destruct (Rmult_integral _ _ product_zero) as [left_zero | right_zero].
    + apply two_squares_zero_iff in left_zero.
      destruct left_zero as [z5_zero z13_zero].
      right; unfold coordinate_plane_b17; repeat split; assumption.
    + apply four_squares_zero_iff in right_zero.
      destruct right_zero as [z17_zero [z18_zero [z19_zero z20_zero]]].
      left; unfold coordinate_plane_a15; repeat split; assumption.
  - intros [plane_a | plane_b].
    + destruct plane_a as [-> [-> [-> [-> [-> ->]]]]].
      unfold quadratic_common_zero; repeat split; ring.
    + destruct plane_b as [z6_zero [z16_zero [z5_zero z13_zero]]].
      subst; unfold quadratic_common_zero; repeat split; ring.
Qed.

Theorem admitted_directions_fail_additive_closure :
  quadratic_common_zero 1 0 0 0 0 0 0 0 /\
  quadratic_common_zero 0 0 0 0 1 0 0 0 /\
  ~ quadratic_common_zero 1 0 0 0 1 0 0 0.
Proof.
  repeat split; unfold quadratic_common_zero; try (repeat split; ring).
  intros [_ [_ [_ [impossible _]]]]; nra.
Qed.

Theorem e11_direction_is_obstructed :
  ~ quadratic_common_zero 0 1 0 0 0 0 0 0.
Proof. intros [impossible _]; nra. Qed.

Print Assumptions two_squares_zero_iff.
Print Assumptions four_squares_zero_iff.
Print Assumptions first_obstruction_norm_identity.
Print Assumptions residual_obstruction_norm_identity.
Print Assumptions selected_quadratic_zero_set.
Print Assumptions admitted_directions_fail_additive_closure.
Print Assumptions e11_direction_is_obstructed.
