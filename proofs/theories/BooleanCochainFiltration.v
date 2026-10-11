(** Boolean polynomial degree under cochain face maps.

    The filtration uses polynomial representatives of bounded total degree.
    A reduced ANF is such a representative; cancellation and Boolean
    idempotence can reduce its degree. The substitution theorem proves the
    bound before either reduction, so either reduction preserves the bound.
    A group-cochain differential over GF(2) is the sum of pullbacks along
    face maps. For XOR groups, each face substitutes linear XOR expressions.
    The theorem applies in every cochain degree and every finite dimension. *)

From Stdlib Require Import Bool Arith Lia List.
Import ListNotations.

Inductive boolean_polynomial : Type :=
| PolynomialZero
| PolynomialOne
| PolynomialVariable (variable : nat)
| PolynomialSum (left right : boolean_polynomial)
| PolynomialProduct (left right : boolean_polynomial).

Fixpoint polynomial_degree (polynomial : boolean_polynomial) : nat :=
  match polynomial with
  | PolynomialZero | PolynomialOne => 0
  | PolynomialVariable _ => 1
  | PolynomialSum left_polynomial right_polynomial =>
      Nat.max (polynomial_degree left_polynomial) (polynomial_degree right_polynomial)
  | PolynomialProduct left_polynomial right_polynomial =>
      polynomial_degree left_polynomial + polynomial_degree right_polynomial
  end.

Fixpoint polynomial_evaluate (polynomial : boolean_polynomial) (point : nat -> bool) : bool :=
  match polynomial with
  | PolynomialZero => false
  | PolynomialOne => true
  | PolynomialVariable variable => point variable
  | PolynomialSum left_polynomial right_polynomial =>
      xorb (polynomial_evaluate left_polynomial point) (polynomial_evaluate right_polynomial point)
  | PolynomialProduct left_polynomial right_polynomial =>
      andb (polynomial_evaluate left_polynomial point) (polynomial_evaluate right_polynomial point)
  end.

Fixpoint polynomial_substitute (polynomial : boolean_polynomial)
    (substitution : nat -> boolean_polynomial) : boolean_polynomial :=
  match polynomial with
  | PolynomialZero => PolynomialZero
  | PolynomialOne => PolynomialOne
  | PolynomialVariable variable => substitution variable
  | PolynomialSum left_polynomial right_polynomial =>
      PolynomialSum (polynomial_substitute left_polynomial substitution)
                    (polynomial_substitute right_polynomial substitution)
  | PolynomialProduct left_polynomial right_polynomial =>
      PolynomialProduct (polynomial_substitute left_polynomial substitution)
                        (polynomial_substitute right_polynomial substitution)
  end.

Theorem linear_substitution_preserves_degree : forall polynomial substitution,
    (forall variable, polynomial_degree (substitution variable) <= 1) ->
    polynomial_degree (polynomial_substitute polynomial substitution) <=
    polynomial_degree polynomial.
Proof.
  induction polynomial; intros substitution linear; simpl; try lia.
  - apply linear.
  - apply Nat.max_le_compat; [apply IHpolynomial1 | apply IHpolynomial2]; exact linear.
  - specialize (IHpolynomial1 substitution linear).
    specialize (IHpolynomial2 substitution linear). lia.
Qed.
Print Assumptions linear_substitution_preserves_degree.

Theorem substitution_evaluation : forall polynomial substitution point,
    polynomial_evaluate (polynomial_substitute polynomial substitution) point =
    polynomial_evaluate polynomial
      (fun variable => polynomial_evaluate (substitution variable) point).
Proof.
  induction polynomial; intros substitution point; simpl; try reflexivity;
    rewrite IHpolynomial1, IHpolynomial2; reflexivity.
Qed.
Print Assumptions substitution_evaluation.

Definition degree_at_most (function : (nat -> bool) -> bool) (bound : nat) : Prop :=
  exists polynomial, polynomial_degree polynomial <= bound /\
    forall point, polynomial_evaluate polynomial point = function point.

Theorem addition_preserves_filtration : forall left right bound,
    degree_at_most left bound -> degree_at_most right bound ->
    degree_at_most (fun point => xorb (left point) (right point)) bound.
Proof.
  intros left right bound [left_poly [left_degree left_value]]
    [right_poly [right_degree right_value]].
  exists (PolynomialSum left_poly right_poly). split; simpl.
  - apply Nat.max_lub; assumption.
  - intros point. rewrite left_value, right_value. reflexivity.
Qed.
Print Assumptions addition_preserves_filtration.

Theorem linear_pullback_preserves_filtration : forall function bound substitution,
    degree_at_most function bound ->
    (forall variable, polynomial_degree (substitution variable) <= 1) ->
    degree_at_most (fun point => function
      (fun variable => polynomial_evaluate (substitution variable) point)) bound.
Proof.
  intros function bound substitution [polynomial [degree value]] linear.
  exists (polynomial_substitute polynomial substitution). split.
  - eapply Nat.le_trans; [apply linear_substitution_preserves_degree; exact linear | exact degree].
  - intros point. rewrite substitution_evaluation. apply value.
Qed.
Print Assumptions linear_pullback_preserves_filtration.

Fixpoint face_sum (polynomial : boolean_polynomial)
    (faces : list (nat -> boolean_polynomial)) : boolean_polynomial :=
  match faces with
  | [] => PolynomialZero
  | face :: remaining => PolynomialSum
      (polynomial_substitute polynomial face) (face_sum polynomial remaining)
  end.

Theorem cochain_differential_preserves_degree : forall polynomial faces,
    Forall (fun face => forall variable, polynomial_degree (face variable) <= 1) faces ->
    polynomial_degree (face_sum polynomial faces) <= polynomial_degree polynomial.
Proof.
  intros polynomial faces linear. induction linear; simpl; [lia |].
  apply Nat.max_lub; [apply linear_substitution_preserves_degree |]; assumption.
Qed.
Print Assumptions cochain_differential_preserves_degree.

(** A cochain is arbitrary. The sign cochain becomes a cocycle only when
    its ordinary coboundary vanishes. The normalized Schreier expression
    below equals that coboundary for any normalized sign cochain. *)
Section Cochain.
  Context {Group : Type} (identity : Group) (add : Group -> Group -> Group).
  Hypothesis add_identity : forall value, add value identity = value.
  Variable sign_cochain : Group -> Group -> bool.
  Hypothesis sign_identity : forall value, sign_cochain value identity = false.

  Definition ordinary_coboundary (left right input : Group) : bool :=
    xorb (xorb (sign_cochain right input) (sign_cochain left (add right input)))
         (xorb (sign_cochain (add left right) input) (sign_cochain left right)).

  Definition schreier_exponent (left right input : Group) : bool :=
    xorb (xorb (sign_cochain right input) (sign_cochain left (add right input)))
         (sign_cochain (add left right) input).

  Theorem normalized_schreier_is_coboundary : forall left right input,
      xorb (schreier_exponent left right input) (schreier_exponent left right identity) =
      ordinary_coboundary left right input.
  Proof.
    intros left right input. unfold schreier_exponent, ordinary_coboundary.
    rewrite add_identity, !sign_identity. simpl.
    destruct (sign_cochain right input), (sign_cochain left (add right input)),
      (sign_cochain (add left right) input), (sign_cochain left right); reflexivity.
  Qed.
  Print Assumptions normalized_schreier_is_coboundary.
End Cochain.

(** Coordinates are flattened into consecutive argument blocks. Face zero
    drops the first argument, internal face i adds arguments i-1 and i by
    XOR, and the last face drops the last argument. Every coordinate
    pullback is a variable or the XOR of two variables. *)
Definition xor_group_face (block_dimension arity face variable : nat) : boolean_polynomial :=
  if Nat.eqb face 0 then PolynomialVariable (variable + block_dimension)
  else if Nat.leb face arity then
    let argument := variable / block_dimension in
    if Nat.ltb argument (face - 1) then PolynomialVariable variable
    else if Nat.eqb argument (face - 1) then
      PolynomialSum (PolynomialVariable variable)
                    (PolynomialVariable (variable + block_dimension))
    else PolynomialVariable (variable + block_dimension)
  else PolynomialVariable variable.

Theorem xor_group_face_linear : forall block_dimension arity face variable,
    polynomial_degree (xor_group_face block_dimension arity face variable) <= 1.
Proof.
  intros block_dimension arity face variable. unfold xor_group_face.
  repeat match goal with
  | |- context [if ?condition then _ else _] => destruct condition
  end; simpl; lia.
Qed.
Print Assumptions xor_group_face_linear.

Definition xor_group_differential (block_dimension arity : nat)
    (polynomial : boolean_polynomial) : boolean_polynomial :=
  face_sum polynomial
    (map (xor_group_face block_dimension arity) (seq 0 (arity + 2))).

Theorem xor_group_differential_preserves_degree : forall block_dimension arity polynomial,
    polynomial_degree (xor_group_differential block_dimension arity polynomial) <=
    polynomial_degree polynomial.
Proof.
  intros block_dimension arity polynomial. unfold xor_group_differential.
  apply cochain_differential_preserves_degree. apply Forall_forall.
  intros face in_faces. apply in_map_iff in in_faces.
  destruct in_faces as [face_index [face_equal _]]. subst face.
  apply xor_group_face_linear.
Qed.
Print Assumptions xor_group_differential_preserves_degree.
