(** Kernel symmetry of the recursive real Cayley-Dickson tower.

    For every order and all a, z of the tower, a z = 0 exactly when z a = 0
    (Biss, Dugger and Isaksen, Corollary 9.3; Moreno 1997, Corollary 1.6).
    The proof follows Lemma 9.2 of Biss, Dugger and Isaksen: the coordinate
    inner product makes L_x adjoint to L_(conj x) and R_y adjoint to
    R_(conj y), conj(x) = 2 re(x) 1 - x turns conj(a) b into
    2 re(a) b - a b, and a vanishing a b then gives
    <conj(a) b, conj(a) b> = <b, a (conj(a) b)> = 0, so conj(a) b = 0 because
    a sum of real squares vanishes only at zero. The same argument on the
    right gives a conj(b) = 0, and conjugating a z = 0 and applying both
    yields z a = 0.

    The inner product is positive definite over the reals, which is where
    the argument uses the coefficient field (tower_inner_self_zero).  This
    file proves nothing over another ring of coefficients.

    No step uses associativity, alternativity or multiplicativity of the
    norm, so the theorem holds at orders 4 and higher, where those fail. *)

From Stdlib Require Import Reals Lra Lia PeanoNat.
From OpenGororoba Require Import RecursiveCDTower.
Local Open Scope R_scope.

Fixpoint tower_one (order : nat) : cd_tower order :=
 match order with O => 1 | S lower => (tower_one lower,tower_zero lower) end.

Fixpoint tower_inner (order : nat) : cd_tower order -> cd_tower order -> R :=
 match order as dimension return cd_tower dimension -> cd_tower dimension -> R with
 | O => Rmult
 | S lower => fun first second =>
   tower_inner lower (fst first) (fst second) + tower_inner lower (snd first) (snd second) end.

Fixpoint tower_coordinate (order : nat) : cd_tower order -> nat -> R :=
 match order as dimension return cd_tower dimension -> nat -> R with
 | O => fun value _ => value
 | S lower => fun value index =>
   if Nat.ltb index (Nat.pow 2 lower) then tower_coordinate lower (fst value) index
   else tower_coordinate lower (snd value) (index - Nat.pow 2 lower) end.

(** Coordinates decide equality, which reduces a vector identity to a real
    identity that ring closes. *)

Lemma tower_coordinate_add order : forall first second index,
 tower_coordinate order (tower_add order first second) index =
 tower_coordinate order first index + tower_coordinate order second index.
Proof.
 induction order as [|order induction_equal]; intros first second index; simpl.
 - reflexivity.
 - destruct (Nat.ltb index (Nat.pow 2 order)); apply induction_equal.
Qed.

Lemma tower_coordinate_neg order : forall value index,
 tower_coordinate order (tower_neg order value) index = - tower_coordinate order value index.
Proof.
 induction order as [|order induction_equal]; intros value index; simpl.
 - reflexivity.
 - destruct (Nat.ltb index (Nat.pow 2 order)); apply induction_equal.
Qed.

Lemma tower_coordinate_scale order factor : forall value index,
 tower_coordinate order (tower_scale order factor value) index = factor * tower_coordinate order value index.
Proof.
 induction order as [|order induction_equal]; intros value index; simpl.
 - reflexivity.
 - destruct (Nat.ltb index (Nat.pow 2 order)); apply induction_equal.
Qed.

Lemma tower_coordinate_zero order : forall index, tower_coordinate order (tower_zero order) index = 0.
Proof.
 induction order as [|order induction_equal]; intro index; simpl.
 - reflexivity.
 - destruct (Nat.ltb index (Nat.pow 2 order)); apply induction_equal.
Qed.

Lemma tower_extensionality order : forall first second,
 (forall index, (index < Nat.pow 2 order)%nat ->
   tower_coordinate order first index = tower_coordinate order second index) ->
 first = second.
Proof.
 induction order as [|order induction_equal]; intros first second coordinates.
 - exact (coordinates O Nat.lt_0_1).
 - destruct first as [first_low first_high], second as [second_low second_high].
   simpl in coordinates. f_equal; apply induction_equal; intros index bound.
   + specialize (coordinates index ltac:(simpl; lia)).
     rewrite (proj2 (Nat.ltb_lt _ _) bound) in coordinates. exact coordinates.
   + specialize (coordinates (index + Nat.pow 2 order)%nat ltac:(simpl; lia)).
     rewrite (proj2 (Nat.ltb_ge _ _)) in coordinates by lia.
     replace (index + Nat.pow 2 order - Nat.pow 2 order)%nat with index in coordinates by lia.
     exact coordinates.
Qed.

Ltac tower_vector :=
 apply tower_extensionality; intros ? _; unfold tower_sub;
 repeat (rewrite tower_coordinate_add || rewrite tower_coordinate_neg ||
         rewrite tower_coordinate_scale || rewrite tower_coordinate_zero);
 ring.

(** Linear structure of conjugation and multiplication. *)

Lemma tower_conj_scale order factor : forall value,
 tower_conj order (tower_scale order factor value) = tower_scale order factor (tower_conj order value).
Proof.
 induction order as [|order induction_equal]; intro value; simpl.
 - reflexivity.
 - rewrite induction_equal. f_equal. tower_vector.
Qed.

Lemma tower_conj_one order : tower_conj order (tower_one order) = tower_one order.
Proof.
 induction order as [|order induction_equal]; simpl.
 - reflexivity.
 - rewrite induction_equal, tower_neg_zero. reflexivity.
Qed.

Lemma tower_mul_linear order :
 (forall first second right, tower_mul order (tower_add order first second) right =
   tower_add order (tower_mul order first right) (tower_mul order second right)) /\
 (forall first second left, tower_mul order left (tower_add order first second) =
   tower_add order (tower_mul order left first) (tower_mul order left second)) /\
 (forall factor value right, tower_mul order (tower_scale order factor value) right =
   tower_scale order factor (tower_mul order value right)) /\
 (forall factor value left, tower_mul order left (tower_scale order factor value) =
   tower_scale order factor (tower_mul order left value)).
Proof.
 induction order as [|order induction_linear]; simpl.
 - repeat split; intros; ring.
 - destruct induction_linear as [add_left [add_right [scale_left scale_right]]].
   repeat split.
   + intros [first_low first_high] [second_low second_high] [right_low right_high]; simpl.
     rewrite ?add_left, ?add_right. f_equal; tower_vector.
   + intros [first_low first_high] [second_low second_high] [left_low left_high]; simpl.
     rewrite ?tower_conj_add, ?add_left, ?add_right. f_equal; tower_vector.
   + intros factor [value_low value_high] [right_low right_high]; simpl.
     rewrite ?scale_left, ?scale_right. f_equal; tower_vector.
   + intros factor [value_low value_high] [left_low left_high]; simpl.
     rewrite ?tower_conj_scale, ?scale_left, ?scale_right. f_equal; tower_vector.
Qed.

Lemma tower_mul_add_left order first second right :
 tower_mul order (tower_add order first second) right =
 tower_add order (tower_mul order first right) (tower_mul order second right).
Proof. apply tower_mul_linear. Qed.

Lemma tower_mul_add_right order left first second :
 tower_mul order left (tower_add order first second) =
 tower_add order (tower_mul order left first) (tower_mul order left second).
Proof. apply tower_mul_linear. Qed.

Lemma tower_mul_scale_left order factor value right :
 tower_mul order (tower_scale order factor value) right = tower_scale order factor (tower_mul order value right).
Proof. apply tower_mul_linear. Qed.

Lemma tower_mul_scale_right order left factor value :
 tower_mul order left (tower_scale order factor value) = tower_scale order factor (tower_mul order left value).
Proof. apply tower_mul_linear. Qed.

Lemma tower_mul_one order :
 (forall value, tower_mul order (tower_one order) value = value) /\
 (forall value, tower_mul order value (tower_one order) = value).
Proof.
 induction order as [|order induction_one]; simpl.
 - split; intros; ring.
 - destruct induction_one as [one_left one_right].
   split; intros [value_low value_high]; simpl;
   rewrite ?tower_conj_zero, ?tower_conj_one, ?one_left, ?one_right,
     ?tower_mul_zero_left, ?tower_mul_zero_right; f_equal; tower_vector.
Qed.

Lemma tower_mul_one_left order value : tower_mul order (tower_one order) value = value.
Proof. apply tower_mul_one. Qed.

Lemma tower_mul_one_right order value : tower_mul order value (tower_one order) = value.
Proof. apply tower_mul_one. Qed.

(** conj(x) = 2 re(x) 1 - x. *)

Lemma tower_add_conj order : forall value,
 tower_add order value (tower_conj order value) =
 tower_scale order (2 * tower_real_part order value) (tower_one order).
Proof.
 induction order as [|order induction_equal]; intro value; simpl.
 - ring.
 - destruct value as [value_low value_high]. simpl.
   rewrite induction_equal, tower_scale_zero. f_equal. tower_vector.
Qed.

Lemma tower_conj_split order value :
 tower_conj order value =
 tower_sub order (tower_scale order (2 * tower_real_part order value) (tower_one order)) value.
Proof.
 rewrite <- tower_add_conj. tower_vector.
Qed.

Lemma tower_conj_mul_left_split order left right :
 tower_mul order (tower_conj order left) right =
 tower_sub order (tower_scale order (2 * tower_real_part order left) right) (tower_mul order left right).
Proof.
 rewrite (tower_conj_split order left). unfold tower_sub.
 rewrite tower_mul_add_left, tower_mul_neg_left, tower_mul_scale_left, tower_mul_one_left. reflexivity.
Qed.

Lemma tower_conj_mul_right_split order left right :
 tower_mul order left (tower_conj order right) =
 tower_sub order (tower_scale order (2 * tower_real_part order right) left) (tower_mul order left right).
Proof.
 rewrite (tower_conj_split order right). unfold tower_sub.
 rewrite tower_mul_add_right, tower_mul_neg_right, tower_mul_scale_right, tower_mul_one_right. reflexivity.
Qed.

(** The coordinate inner product: bilinear over the reals (additive and
    homogeneous in each argument), symmetric and positive definite. *)

Lemma tower_inner_linear order :
 (forall first second right, tower_inner order (tower_add order first second) right =
   tower_inner order first right + tower_inner order second right) /\
 (forall first second left, tower_inner order left (tower_add order first second) =
   tower_inner order left first + tower_inner order left second) /\
 (forall value right, tower_inner order (tower_neg order value) right = - tower_inner order value right) /\
 (forall value left, tower_inner order left (tower_neg order value) = - tower_inner order left value).
Proof.
 induction order as [|order induction_linear]; simpl.
 - repeat split; intros; ring.
 - destruct induction_linear as [add_left [add_right [neg_left neg_right]]].
   repeat split; intros; cbn [tower_inner tower_add tower_neg fst snd];
   rewrite ?add_left, ?add_right, ?neg_left, ?neg_right; ring.
Qed.

Lemma tower_inner_add_left order first second right :
 tower_inner order (tower_add order first second) right =
 tower_inner order first right + tower_inner order second right.
Proof. apply tower_inner_linear. Qed.

Lemma tower_inner_add_right order left first second :
 tower_inner order left (tower_add order first second) =
 tower_inner order left first + tower_inner order left second.
Proof. apply tower_inner_linear. Qed.

Lemma tower_inner_neg_left order value right :
 tower_inner order (tower_neg order value) right = - tower_inner order value right.
Proof. apply tower_inner_linear. Qed.

Lemma tower_inner_neg_right order left value :
 tower_inner order left (tower_neg order value) = - tower_inner order left value.
Proof. apply tower_inner_linear. Qed.

Lemma tower_inner_scale order :
 (forall factor value right, tower_inner order (tower_scale order factor value) right =
   factor * tower_inner order value right) /\
 (forall left factor value, tower_inner order left (tower_scale order factor value) =
   factor * tower_inner order left value).
Proof.
 induction order as [|order induction_scale]; simpl.
 - split; intros; ring.
 - destruct induction_scale as [scale_left scale_right].
   split; intros; cbn [tower_inner tower_scale fst snd];
   rewrite ?scale_left, ?scale_right; ring.
Qed.

Lemma tower_inner_scale_left order factor value right :
 tower_inner order (tower_scale order factor value) right = factor * tower_inner order value right.
Proof. apply tower_inner_scale. Qed.

Lemma tower_inner_scale_right order left factor value :
 tower_inner order left (tower_scale order factor value) = factor * tower_inner order left value.
Proof. apply tower_inner_scale. Qed.

Lemma tower_inner_symmetric order : forall first second,
 tower_inner order first second = tower_inner order second first.
Proof.
 induction order as [|order induction_equal]; intros first second; simpl.
 - ring.
 - rewrite (induction_equal (fst first)), (induction_equal (snd first)). reflexivity.
Qed.

Lemma tower_inner_zero_left order : forall value, tower_inner order (tower_zero order) value = 0.
Proof.
 induction order as [|order induction_equal]; intro value; simpl.
 - ring.
 - rewrite !induction_equal. ring.
Qed.

Lemma tower_inner_zero_right order value : tower_inner order value (tower_zero order) = 0.
Proof. rewrite tower_inner_symmetric. apply tower_inner_zero_left. Qed.

Lemma tower_inner_self_nonnegative order : forall value, 0 <= tower_inner order value value.
Proof.
 induction order as [|order induction_nonnegative]; intro value; simpl.
 - apply Rle_0_sqr.
 - pose proof (induction_nonnegative (fst value)). pose proof (induction_nonnegative (snd value)). lra.
Qed.

Lemma tower_inner_self_zero order : forall value,
 tower_inner order value value = 0 -> value = tower_zero order.
Proof.
 induction order as [|order induction_zero]; intros value vanishing; simpl in *.
 - destruct (Rmult_integral _ _ vanishing); assumption.
 - destruct value as [value_low value_high]. simpl in vanishing.
   pose proof (tower_inner_self_nonnegative order value_low).
   pose proof (tower_inner_self_nonnegative order value_high).
   rewrite (induction_zero value_low), (induction_zero value_high) by lra. reflexivity.
Qed.

(** Biss, Dugger and Isaksen, Lemma 3.4 (Moreno 1997, Lemma 1.3): L_x has
    adjoint L_(conj x) and R_y has adjoint R_(conj y). *)

Theorem tower_inner_adjoint order :
 (forall left value test, tower_inner order (tower_mul order left value) test =
   tower_inner order value (tower_mul order (tower_conj order left) test)) /\
 (forall value right test, tower_inner order (tower_mul order value right) test =
   tower_inner order value (tower_mul order test (tower_conj order right))).
Proof.
 induction order as [|order induction_adjoint]; simpl.
 - split; intros; ring.
 - destruct induction_adjoint as [adjoint_left adjoint_right].
   split; intros [x1 x2] [y1 y2] [z1 z2];
   cbn [tower_mul tower_conj tower_inner fst snd]; unfold tower_sub;
   rewrite ?tower_conj_neg, ?tower_conj_involution, ?tower_mul_neg_left, ?tower_mul_neg_right,
     ?tower_neg_involution;
   rewrite ?tower_inner_add_left, ?tower_inner_add_right, ?tower_inner_neg_left, ?tower_inner_neg_right.
   + pose proof (adjoint_left x1 y1 z1) as low_low.
     pose proof (adjoint_left (tower_conj order y2) x2 z1) as high_low.
     rewrite tower_conj_involution in high_low.
     pose proof (adjoint_right x2 (tower_conj order z1) y2) as high_low_swap.
     rewrite tower_conj_involution, (tower_inner_symmetric order _ y2) in high_low_swap.
     pose proof (adjoint_right y2 x1 z2) as low_high.
     pose proof (adjoint_right x2 (tower_conj order y1) z2) as high_high.
     rewrite tower_conj_involution in high_high.
     pose proof (adjoint_left (tower_conj order z2) x2 y1) as high_high_swap.
     rewrite tower_conj_involution, (tower_inner_symmetric order _ y1) in high_high_swap.
     lra.
   + pose proof (adjoint_right x1 y1 z1) as low_low.
     pose proof (adjoint_left (tower_conj order y2) x2 z1) as high_low.
     rewrite tower_conj_involution in high_low.
     pose proof (adjoint_left y2 x1 z2) as low_high.
     pose proof (adjoint_right x2 (tower_conj order y1) z2) as high_high.
     rewrite tower_conj_involution in high_high.
     lra.
Qed.

Lemma tower_inner_adjoint_left order left value test :
 tower_inner order (tower_mul order left value) test =
 tower_inner order value (tower_mul order (tower_conj order left) test).
Proof. apply tower_inner_adjoint. Qed.

Lemma tower_inner_adjoint_right order value right test :
 tower_inner order (tower_mul order value right) test =
 tower_inner order value (tower_mul order test (tower_conj order right)).
Proof. apply tower_inner_adjoint. Qed.

(** Biss, Dugger and Isaksen, Lemma 9.2: a b = 0 gives conj(a) b = 0 and
    a conj(b) = 0. *)

Lemma tower_conj_left_zero order left right :
 tower_mul order left right = tower_zero order ->
 tower_mul order (tower_conj order left) right = tower_zero order.
Proof.
 intro vanishing. apply tower_inner_self_zero.
 rewrite tower_inner_adjoint_left, tower_conj_involution, tower_conj_mul_left_split, vanishing.
 unfold tower_sub.
 rewrite tower_neg_zero, tower_mul_add_right, tower_mul_scale_right, vanishing, tower_mul_zero_right,
   tower_scale_zero, tower_inner_add_right, !tower_inner_zero_right.
 ring.
Qed.

Lemma tower_conj_right_zero order left right :
 tower_mul order left right = tower_zero order ->
 tower_mul order left (tower_conj order right) = tower_zero order.
Proof.
 intro vanishing. apply tower_inner_self_zero.
 rewrite tower_inner_adjoint_right, tower_conj_involution, tower_conj_mul_right_split, vanishing.
 unfold tower_sub.
 rewrite tower_neg_zero, tower_mul_add_left, tower_mul_scale_left, vanishing, tower_mul_zero_left,
   tower_scale_zero, tower_inner_add_right, !tower_inner_zero_right.
 ring.
Qed.

(** Biss, Dugger and Isaksen, Corollary 9.3: a z = 0 exactly when z a = 0. *)

Theorem tower_kernel_swap order operand vector :
 tower_mul order operand vector = tower_zero order ->
 tower_mul order vector operand = tower_zero order.
Proof.
 intro vanishing.
 pose proof (f_equal (tower_conj order) vanishing) as conjugated.
 rewrite tower_conj_antimorphism, tower_conj_zero in conjugated.
 apply tower_conj_left_zero in conjugated. rewrite tower_conj_involution in conjugated.
 apply tower_conj_right_zero in conjugated. rewrite tower_conj_involution in conjugated.
 exact conjugated.
Qed.

Theorem tower_kernel_equality order operand vector :
 tower_mul order operand vector = tower_zero order <->
 tower_mul order vector operand = tower_zero order.
Proof. split; apply tower_kernel_swap. Qed.

Print Assumptions tower_inner_adjoint.
Print Assumptions tower_kernel_equality.
