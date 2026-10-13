(** * Sedenion zero and explicit nonzero annihilator witnesses.

    C014_zero_annihilates proves sed_mul sed_zero a = sed_zero for every
    sedenion a. C014_nonzero_annihilator_exists proves the explicit product
    sed_mul sed_zd_b sed_zd_a = sed_zero together with sed_zd_b <> sed_zero.
    The declarations establish these two products; an annihilator dimension
    or closure property requires a separate theorem. *)

From OpenGororoba Require Import Prelude CayleyDicksonAlgebra Sedenion OctonionNorm CDNegLemmas.
From OpenGororobaVerified Require Import C908_SedenionZeroDivisor.

(** Zero annihilates everything: 0 * a = 0. *)
Theorem C014_zero_annihilates : forall a : CDSed,
  sed_mul sed_zero a = sed_zero.
Proof.
  exact sed_mul_zero_left.
Qed.

(** The Moreno-Froloff witness provides one nonzero annihilator. *)
Theorem C014_nonzero_annihilator_exists :
  sed_mul sed_zd_b sed_zd_a = sed_zero /\ sed_zd_b <> sed_zero.
Proof.
  split.
  - exact sed_zd_product_zero_rev.
  - exact sed_zd_b_nonzero.
Qed.
