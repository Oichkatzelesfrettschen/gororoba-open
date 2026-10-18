(** Associator phases under highest-bit Cayley-Dickson doubling.
    Boolean true denotes coefficient -1. The phase compares bracketings of
    basis units; matrix composition remains associative. Walsh sums are
    unnormalized integer amplitudes, distinct from the ANF transform. *)
From Stdlib Require Import Arith Lia Bool ZArith ZArithRing btauto.Btauto.
From OpenGororoba Require Import SchreierSignCode.

Definition associator_phase order (left middle right : cube order) : bool :=
  xorb (schreier order left middle right) (sign_exponent order left middle).
Definition commutation_phase order (left right : cube order) : bool :=
  xorb (sign_exponent order left right) (sign_exponent order right left).

Theorem sign_doubling : forall order (left right : cube order) left_high right_high,
  sign_exponent (S order) (left, left_high) (right, right_high) =
  xorb (sign_exponent order left right)
    (xorb (andb right_high (commutation_phase order left right))
      (xorb (andb left_high (cube_nonzero order right)) (andb left_high right_high))).
Proof.
  intros. cbn [sign_exponent fst snd]. unfold commutation_phase.
  destruct left_high, right_high; simpl; btauto.
Qed.

(** Every product of two high bits cancels in the four sign factors. *)
Theorem associator_doubling : forall order (left middle right : cube order)
  left_high middle_high right_high,
  associator_phase (S order) (left, left_high) (middle, middle_high) (right, right_high) =
  xorb (associator_phase order left middle right)
    (xorb (andb left_high
      (xorb (cube_nonzero order middle)
        (xorb (cube_nonzero order right) (cube_nonzero order (cube_xor order middle right)))))
    (xorb (andb middle_high
      (xorb (commutation_phase order left middle)
        (commutation_phase order left (cube_xor order middle right))))
      (andb right_high
        (xorb (commutation_phase order (cube_xor order left middle) right)
          (xorb (commutation_phase order middle right)
            (commutation_phase order left (cube_xor order middle right))))))).
Proof.
  intros. unfold associator_phase, schreier.
  cbn [cube_xor fst snd]. rewrite !sign_doubling. btauto.
Qed.

Definition pair_coefficient order (left right : cube order) :=
  xorb (cube_nonzero order left)
    (xorb (cube_nonzero order right) (cube_nonzero order (cube_xor order left right))).

Theorem lower_pair_lifting : forall order (left middle right : cube order) high,
  associator_phase (S order) (left, false) (middle, false) (right, high) =
  xorb (associator_phase order left middle right)
    (andb high (pair_coefficient order left middle)).
Proof.
  intros order left middle right high.
  pose proof (schreier_high_difference order left middle right false false) as derivative.
  unfold associator_phase. destruct high.
  - cbn [sign_exponent fst snd].
    change (xorb (schreier (S order) (left, false) (middle, false) (right, false))
      (schreier (S order) (left, false) (middle, false) (right, true)) =
      pair_coefficient order left middle) in derivative.
    assert (low_slice : schreier (S order) (left, false) (middle, false) (right, false) =
      schreier order left middle right).
    { unfold schreier. cbn [sign_exponent cube_xor fst snd]. btauto. }
    rewrite low_slice in derivative.
    rewrite <- derivative. btauto.
  - unfold schreier. cbn [sign_exponent cube_xor fst snd]. btauto.
Qed.

Lemma xor_nonzero_of_distinct : forall order (left right : cube order),
  left <> right -> cube_nonzero order (cube_xor order left right) = true.
Proof.
  intros order left right distinct. unfold cube_nonzero.
  rewrite cube_equal_translate, cube_xor_zero.
  destruct (cube_equal order right left) eqn:equal; [|reflexivity].
  apply cube_equal_spec in equal. symmetry in equal. contradiction.
Qed.

Theorem independent_pair_coefficient : forall order (left right : cube order),
  cube_nonzero order left = true -> cube_nonzero order right = true -> left <> right ->
  pair_coefficient order left right = true.
Proof.
  intros order left right left_nonzero right_nonzero distinct.
  unfold pair_coefficient. rewrite left_nonzero, right_nonzero,
    (xor_nonzero_of_distinct order left right distinct). reflexivity.
Qed.

Open Scope Z_scope.
Definition phase_sign (phase : bool) : Z := if phase then -1 else 1.
Lemma phase_sign_xor : forall left right,
  phase_sign (xorb left right) = phase_sign left * phase_sign right.
Proof. intros [] []; reflexivity. Qed.

Theorem independent_pair_cancellation : forall order (left middle right : cube order),
  cube_nonzero order left = true -> cube_nonzero order middle = true -> left <> middle ->
  phase_sign (associator_phase (S order) (left, false) (middle, false) (right, false)) +
  phase_sign (associator_phase (S order) (left, false) (middle, false) (right, true)) = 0.
Proof.
  intros order left middle right left_nonzero middle_nonzero distinct.
  rewrite !lower_pair_lifting,
    (independent_pair_coefficient order left middle left_nonzero middle_nonzero distinct).
  destruct (associator_phase order left middle right); reflexivity.
Qed.

Fixpoint integer_cube_sum order : (cube order -> Z) -> Z :=
  match order with
  | O => fun function => function tt
  | S lower => fun function => integer_cube_sum lower (fun input => function (input, false)) +
      integer_cube_sum lower (fun input => function (input, true))
  end.
Fixpoint cube_dot order : cube order -> cube order -> bool :=
  match order with
  | O => fun _ _ => false
  | S lower => fun frequency input => xorb (cube_dot lower (fst frequency) (fst input))
      (andb (snd frequency) (snd input))
  end.
Definition walsh order (function : cube order -> bool) (frequency : cube order) : Z :=
  integer_cube_sum order (fun input => phase_sign (xorb (function input) (cube_dot order frequency input))).

Lemma integer_cube_sum_ext : forall order first second,
  (forall input, first input = second input) -> integer_cube_sum order first = integer_cube_sum order second.
Proof.
  induction order; intros first second equal; simpl; [apply equal|].
  rewrite (IHorder _ _ (fun input => equal (input, false))),
    (IHorder _ _ (fun input => equal (input, true))). reflexivity.
Qed.
Lemma integer_cube_sum_scale : forall order factor function,
  integer_cube_sum order (fun input => factor * function input) = factor * integer_cube_sum order function.
Proof.
  induction order; intros; simpl; [reflexivity|]. rewrite !IHorder. ring.
Qed.

(** Appending a parity bit moves the spectrum to one slice exactly. *)
Theorem walsh_parity_extension : forall order function coefficient frequency frequency_high,
  walsh (S order) (fun input => xorb (function (fst input)) (andb (snd input) coefficient))
    (frequency, frequency_high) =
  if Bool.eqb frequency_high coefficient then 2 * walsh order function frequency else 0.
Proof.
  intros. unfold walsh. cbn [integer_cube_sum cube_dot fst snd].
  replace (integer_cube_sum order (fun input =>
    phase_sign (xorb (xorb (function input) (andb false coefficient))
      (xorb (cube_dot order frequency input) (andb frequency_high false)))))
    with (integer_cube_sum order (fun input => phase_sign (xorb (function input) (cube_dot order frequency input)))).
  2: { apply integer_cube_sum_ext. intros. f_equal. btauto. }
  replace (integer_cube_sum order (fun input =>
    phase_sign (xorb (xorb (function input) (andb true coefficient))
      (xorb (cube_dot order frequency input) (andb frequency_high true)))))
    with (phase_sign (xorb coefficient frequency_high) *
      integer_cube_sum order (fun input => phase_sign (xorb (function input) (cube_dot order frequency input)))).
  2: { rewrite <- integer_cube_sum_scale. apply integer_cube_sum_ext. intros.
       rewrite <- phase_sign_xor. f_equal. btauto. }
  destruct frequency_high, coefficient; cbn [Bool.eqb xorb phase_sign]; ring.
Qed.

Theorem associator_walsh_lifting : forall order (left middle frequency : cube order) frequency_high,
  walsh (S order) (fun input => associator_phase (S order) (left, false) (middle, false) input)
    (frequency, frequency_high) =
  if Bool.eqb frequency_high (pair_coefficient order left middle)
  then 2 * walsh order (associator_phase order left middle) frequency else 0.
Proof.
  intros. rewrite <- walsh_parity_extension. unfold walsh.
  apply integer_cube_sum_ext. intros [input high]. rewrite lower_pair_lifting. reflexivity.
Qed.

Print Assumptions associator_doubling.
Print Assumptions lower_pair_lifting.
Print Assumptions independent_pair_cancellation.
Print Assumptions walsh_parity_extension.
Print Assumptions associator_walsh_lifting.

Theorem degenerate_pair_coefficient : forall order (value : cube order),
  pair_coefficient order (cube_zero order) value = false /\
  pair_coefficient order value (cube_zero order) = false /\
  pair_coefficient order value value = false.
Proof.
  intros order value. unfold pair_coefficient.
  rewrite cube_nonzero_zero, cube_xor_zero,
    (cube_xor_commutative order (cube_zero order) value), cube_xor_zero.
  assert (self_zero : cube_nonzero order (cube_xor order value value) = false).
  { unfold cube_nonzero. rewrite cube_equal_translate, cube_xor_zero,
      cube_equal_reflexive. reflexivity. }
  rewrite self_zero. destruct (cube_nonzero order value); repeat split; reflexivity.
Qed.

(** Quaternion indices 1 and 2 become the octonion high-bit parity. *)
Example quaternion_pair_zero : forall input : cube 2,
  associator_phase 2 ((tt, true), false) ((tt, false), true) input = false.
Proof. intros [[[] []] []]; reflexivity. Qed.
Example octonion_pair_parity : forall input : cube 2, forall high,
  associator_phase 3 (((tt, true), false), false) (((tt, false), true), false)
    (input, high) = high.
Proof. intros. rewrite lower_pair_lifting, quaternion_pair_zero. destruct high; reflexivity. Qed.
Example degenerate_walsh_slice :
  walsh 1 (fun _ => false) (tt, true) = 0.
Proof. reflexivity. Qed.

Print Assumptions sign_doubling.
Print Assumptions independent_pair_coefficient.
Print Assumptions degenerate_pair_coefficient.

(** Repeated embeddings retain the lower pair and expose every appended bit. *)
Fixpoint cube_append order extra : cube order -> cube extra -> cube (extra + order) :=
  match extra with
  | O => fun value _ => value
  | S smaller => fun value tail => (cube_append order smaller value (fst tail), snd tail)
  end.
Fixpoint constant_cube extra (coefficient : bool) : cube extra :=
  match extra with O => tt | S smaller => (constant_cube smaller coefficient, coefficient) end.
Definition cube_embed order extra (value : cube order) :=
  cube_append order extra value (constant_cube extra false).
Fixpoint cube_parity extra : cube extra -> bool :=
  match extra with O => fun _ => false | S smaller => fun value =>
    xorb (cube_parity smaller (fst value)) (snd value) end.
Lemma pair_coefficient_low : forall order (left right : cube order),
  pair_coefficient (S order) (left, false) (right, false) = pair_coefficient order left right.
Proof.
  intros. unfold pair_coefficient. cbn [cube_xor fst snd].
  rewrite !cube_nonzero_double. now rewrite !orb_false_r.
Qed.
Lemma pair_coefficient_embed : forall extra order (left right : cube order),
  pair_coefficient (extra + order) (cube_embed order extra left) (cube_embed order extra right) =
  pair_coefficient order left right.
Proof.
  induction extra; intros; [reflexivity|].
  change (pair_coefficient (S (extra + order))
    (cube_embed order extra left, false) (cube_embed order extra right, false) = pair_coefficient order left right).
  rewrite pair_coefficient_low. apply IHextra.
Qed.
Theorem associator_iterated_lifting : forall extra order (left middle input : cube order) tail,
  associator_phase (extra + order) (cube_embed order extra left) (cube_embed order extra middle)
    (cube_append order extra input tail) =
  xorb (associator_phase order left middle input)
    (andb (cube_parity extra tail) (pair_coefficient order left middle)).
Proof.
  induction extra; intros order left middle input tail.
  - cbn [cube_embed cube_append cube_parity constant_cube Nat.add]. btauto.
  - destruct tail as [tail high].
    change (associator_phase (S (extra + order))
      (cube_embed order extra left, false) (cube_embed order extra middle, false)
      (cube_append order extra input tail, high) = xorb (associator_phase order left middle input) (andb (cube_parity (S extra) (tail, high)) (pair_coefficient order left middle))).
    rewrite lower_pair_lifting, pair_coefficient_embed, IHextra.
    cbn [cube_parity fst snd]. btauto.
Qed.
Fixpoint parity_extension order extra (function : cube order -> bool) coefficient : cube (extra + order) -> bool :=
  match extra with
  | O => function
  | S smaller => fun value => xorb (parity_extension order smaller function coefficient (fst value))
      (andb (snd value) coefficient)
  end.
Theorem walsh_iterated_parity : forall extra order function coefficient frequency tail,
  walsh (extra + order) (parity_extension order extra function coefficient)
    (cube_append order extra frequency tail) =
  if cube_equal extra tail (constant_cube extra coefficient)
  then (Z.of_nat (Nat.pow 2 extra) * walsh order function frequency)%Z else 0%Z.
Proof.
  induction extra; intros order function coefficient frequency tail.
  - cbn [parity_extension cube_append cube_equal Nat.add Nat.pow Z.of_nat]. ring.
  - destruct tail as [tail high].
    change (walsh (S (extra + order))
      (fun value => xorb (parity_extension order extra function coefficient (fst value))
        (andb (snd value) coefficient)) (cube_append order extra frequency tail, high) = if cube_equal (S extra) (tail, high) (constant_cube (S extra) coefficient) then (Z.of_nat (Nat.pow 2 (S extra)) * walsh order function frequency)%Z else 0%Z).
    rewrite walsh_parity_extension, IHextra.
    cbn [cube_equal constant_cube fst snd].
    destruct (Bool.eqb high coefficient), (cube_equal extra tail (constant_cube extra coefficient));
      cbn [andb]; rewrite ?Nat.pow_succ_r', ?Nat2Z.inj_mul; cbn [Z.of_nat]; ring.
Qed.
Lemma associator_iterated_function : forall extra order (left middle : cube order) input,
  associator_phase (extra + order) (cube_embed order extra left) (cube_embed order extra middle) input =
  parity_extension order extra (associator_phase order left middle) (pair_coefficient order left middle) input.
Proof.
  induction extra; intros; [reflexivity|]. destruct input as [input high].
  change (associator_phase (S (extra + order)) (cube_embed order extra left, false)
    (cube_embed order extra middle, false) (input, high) = parity_extension order (S extra) (associator_phase order left middle) (pair_coefficient order left middle) (input, high)).
  rewrite lower_pair_lifting, pair_coefficient_embed, IHextra. reflexivity.
Qed.
Theorem associator_iterated_walsh : forall extra order (left middle frequency : cube order) tail,
  walsh (extra + order)
    (associator_phase (extra + order) (cube_embed order extra left) (cube_embed order extra middle))
    (cube_append order extra frequency tail) =
  if cube_equal extra tail (constant_cube extra (pair_coefficient order left middle))
  then (Z.of_nat (Nat.pow 2 extra) * walsh order (associator_phase order left middle) frequency)%Z else 0%Z.
Proof.
  intros. rewrite <- walsh_iterated_parity. unfold walsh.
  apply integer_cube_sum_ext. intro input. rewrite associator_iterated_function. reflexivity.
Qed.
Print Assumptions associator_iterated_lifting.
Print Assumptions walsh_iterated_parity.
Print Assumptions associator_iterated_walsh.
