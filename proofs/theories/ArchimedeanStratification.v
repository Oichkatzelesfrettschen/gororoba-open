(** * Equal-square consequence of two real scalar equations.

    For real alpha, beta, gamma, and delta, the equations
    alpha*gamma = beta*delta and alpha*delta = beta*gamma imply
    alpha^2 = beta^2 when gamma and delta are nonzero. The corollary
    excludes that conjunction when the squares differ.

    The checked statements contain neither Cayley-Dickson multiplication
    nor a surreal or general-field domain. Identifying the scalar
    equations with a chosen two-blade product requires its sign
    calculation. Extending the result to another coefficient field
    requires a corresponding formal statement and assumptions.

    Distinct nonzero rational magnitudes share one Archimedean class.
    Finite dyadic examples therefore establish finite scaling behavior,
    while a surreal-stratification claim needs a separate geometric
    specification and proof. *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Theorem zd_cross_ratio :
  forall alpha beta gamma delta : R,
  alpha * gamma = beta * delta ->
  alpha * delta = beta * gamma ->
  gamma <> 0 ->
  delta <> 0 ->
  alpha * alpha = beta * beta.
Proof.
  intros alpha beta gamma delta H1 H2 Hg Hd.

  assert (Hgd : gamma * delta <> 0).
  { intro Habs. apply Rmult_integral in Habs. destruct Habs; contradiction. }
  assert (H3 : alpha * gamma * (alpha * delta) = beta * delta * (beta * gamma)).
  { rewrite H1, H2. ring. }
  assert (H4 : alpha * alpha * (gamma * delta) = beta * beta * (gamma * delta)).
  { ring_simplify in H3. ring_simplify. lra. }
  apply Rmult_eq_reg_r in H4; [exact H4 | exact Hgd].
Qed.

Corollary no_zd_different_scales :
  forall alpha beta gamma delta : R,
  alpha * alpha <> beta * beta ->
  gamma <> 0 ->
  delta <> 0 ->
  ~(alpha * gamma = beta * delta /\ alpha * delta = beta * gamma).
Proof.
  intros alpha beta gamma delta Hneq Hg Hd [H1 H2].
  apply Hneq.
  exact (zd_cross_ratio alpha beta gamma delta H1 H2 Hg Hd).
Qed.

Print Assumptions zd_cross_ratio.
Print Assumptions no_zd_different_scales.
