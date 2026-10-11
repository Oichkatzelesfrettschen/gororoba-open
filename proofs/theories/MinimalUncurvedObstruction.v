(** * Minimal uncurved arity-three identity forces associativity.

    Rearranging the Stasheff relation puts the associator equal to terms
    containing m1. Multilinearity makes m3 vanish when any input is zero.
    Signs of those boundary terms do not affect the minimal case. *)

From Stdlib Require Import Reals Lra.
From OpenGororoba Require Import CayleyDicksonAlgebra Sedenion.

Section MinimalIdentity.
  Context {Vector : Type}.
  Variable zero : Vector.
  Variable add : Vector -> Vector -> Vector.
  Variable negate : Vector -> Vector.
  Hypothesis add_zero : forall value, add value zero = value.
  Hypothesis negate_zero : negate zero = zero.
  Variable m1 : Vector -> Vector.
  Variable m2 : Vector -> Vector -> Vector.
  Variable m3 : Vector -> Vector -> Vector -> Vector.
  Hypothesis minimal : forall value, m1 value = zero.
  Hypothesis m3_zero_left : forall second third, m3 zero second third = zero.
  Hypothesis m3_zero_middle : forall first third, m3 first zero third = zero.
  Hypothesis m3_zero_right : forall first second, m3 first second zero = zero.

  Definition uncurved_arity_three : Prop :=
    forall first second third,
      m2 (m2 first second) third =
      add (m2 first (m2 second third))
        (add (negate (m1 (m3 first second third)))
          (add (negate (m3 (m1 first) second third))
            (add (negate (m3 first (m1 second) third))
                 (negate (m3 first second (m1 third)))))).

  Theorem minimal_uncurved_multiplication_associative :
    uncurved_arity_three ->
    forall first second third,
      m2 (m2 first second) third = m2 first (m2 second third).
  Proof.
    intros identity first second third.
    specialize (identity first second third).
    repeat rewrite minimal in identity.
    rewrite m3_zero_left, m3_zero_middle, m3_zero_right in identity.
    repeat rewrite negate_zero in identity.
    repeat rewrite add_zero in identity.
    exact identity.
  Qed.
End MinimalIdentity.
Print Assumptions minimal_uncurved_multiplication_associative.

(** The same octonionic basis witness embeds in the sedenions. *)
Theorem sedenion_product_nonassociative :
  sed_mul (sed_mul (sed_e 1) (sed_e 2)) (sed_e 4) <>
  sed_mul (sed_e 1) (sed_mul (sed_e 2) (sed_e 4)).
Proof.
  intro associative_witness.
  pose proof (f_equal (fun value => qd (oct_hi (sed_lo value)))
                     associative_witness) as coordinate_equality.
  cbv [sed_mul sed_e sed_zero oct_mul oct_conj oct_e oct_zero
       quat_mul quat_add quat_neg quat_conj quat_zero quat_one
       sed_lo sed_hi oct_lo oct_hi qa qb qc qd] in coordinate_equality.
  lra.
Qed.
Print Assumptions sedenion_product_nonassociative.
