(** Recursive real Cayley-Dickson pairs use the highest bit for doubling. *)
From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.
Fixpoint cd_tower (order : nat) : Type :=
 match order with O => R | S lower => (cd_tower lower * cd_tower lower)%type end.
Fixpoint tower_zero (order : nat) : cd_tower order :=
 match order with O => 0 | S lower => (tower_zero lower,tower_zero lower) end.
Fixpoint tower_add (order : nat) : cd_tower order -> cd_tower order -> cd_tower order :=
 match order as dimension return cd_tower dimension -> cd_tower dimension -> cd_tower dimension with
 | O => Rplus
 | S lower => fun first second =>
   (tower_add lower (fst first) (fst second),tower_add lower (snd first) (snd second)) end.
Fixpoint tower_neg (order : nat) : cd_tower order -> cd_tower order :=
 match order as dimension return cd_tower dimension -> cd_tower dimension with
 | O => Ropp
 | S lower => fun value => (tower_neg lower (fst value),tower_neg lower (snd value)) end.
Definition tower_sub order first second := tower_add order first (tower_neg order second).
Fixpoint tower_scale (order : nat) (factor : R) : cd_tower order -> cd_tower order :=
 match order as dimension return cd_tower dimension -> cd_tower dimension with
 | O => fun value => factor * value
 | S lower => fun value => (tower_scale lower factor (fst value),tower_scale lower factor (snd value)) end.
Fixpoint tower_conj (order : nat) : cd_tower order -> cd_tower order :=
 match order as dimension return cd_tower dimension -> cd_tower dimension with
 | O => fun value => value
 | S lower => fun value => (tower_conj lower (fst value),tower_neg lower (snd value)) end.
Fixpoint tower_mul (order : nat) : cd_tower order -> cd_tower order -> cd_tower order :=
 match order as dimension return cd_tower dimension -> cd_tower dimension -> cd_tower dimension with
 | O => Rmult
 | S lower => fun first second =>
   (tower_sub lower (tower_mul lower (fst first) (fst second))
      (tower_mul lower (tower_conj lower (snd second)) (snd first)),
    tower_add lower (tower_mul lower (snd second) (fst first))
      (tower_mul lower (snd first) (tower_conj lower (fst second)))) end.
Fixpoint tower_real_part (order : nat) : cd_tower order -> R :=
 match order as dimension return cd_tower dimension -> R with
 | O => fun value => value | S lower => fun value => tower_real_part lower (fst value) end.
Definition tower_pure order value := tower_real_part order value = 0.
Lemma tower_add_comm order : forall first second,
 tower_add order first second = tower_add order second first.
Proof.
 induction order as [|order induction_equal]; intros first second.
 - apply Rplus_comm.
 - destruct first, second; simpl. f_equal; apply induction_equal.
Qed.
Lemma tower_add_assoc order : forall first second third,
 tower_add order (tower_add order first second) third = tower_add order first (tower_add order second third).
Proof.
 induction order as [|order induction_equal]; intros first second third.
 - apply Rplus_assoc.
 - destruct first, second, third; simpl. rewrite !induction_equal. reflexivity.
Qed.
Lemma tower_add_zero order : forall value, tower_add order (tower_zero order) value = value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply Rplus_0_l.
 - destruct value; simpl. rewrite !induction_equal. reflexivity.
Qed.
Lemma tower_neg_involution order : forall value, tower_neg order (tower_neg order value) = value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply Ropp_involutive.
 - destruct value; simpl. rewrite !induction_equal. reflexivity.
Qed.
Lemma tower_neg_zero order : tower_neg order (tower_zero order) = tower_zero order.
Proof. induction order as [|order induction_equal]; simpl; [ring|rewrite induction_equal; reflexivity]. Qed.
Lemma tower_neg_add order : forall first second,
 tower_neg order (tower_add order first second) = tower_add order (tower_neg order first) (tower_neg order second).
Proof.
 induction order as [|order induction_equal]; intros first second.
 - apply Ropp_plus_distr.
 - destruct first, second; simpl. rewrite !induction_equal. reflexivity.
Qed.
Lemma tower_add_neg order : forall value, tower_add order value (tower_neg order value) = tower_zero order.
Proof.
 induction order as [|order induction_equal]; intro value.
 - apply Rplus_opp_r.
 - destruct value; simpl. rewrite !induction_equal. reflexivity.
Qed.
Lemma tower_conj_zero order : tower_conj order (tower_zero order) = tower_zero order.
Proof. induction order as [|order induction_equal]; simpl; [reflexivity|rewrite induction_equal, tower_neg_zero; reflexivity]. Qed.
Lemma tower_zero_absorption order :
 (forall value, tower_mul order value (tower_zero order) = tower_zero order) /\
 (forall value, tower_mul order (tower_zero order) value = tower_zero order).
Proof.
 induction order as [|order [zero_right zero_left]].
 - split; intro value; simpl; ring.
 - split; intros [low high]; simpl; unfold tower_sub;
   repeat rewrite tower_conj_zero; repeat rewrite zero_right; repeat rewrite zero_left;
   rewrite tower_neg_zero, tower_add_zero; reflexivity.
Qed.
Lemma tower_mul_zero_right order : forall value, tower_mul order value (tower_zero order) = tower_zero order.
Proof. exact (proj1 (tower_zero_absorption order)). Qed.
Lemma tower_mul_zero_left order : forall value, tower_mul order (tower_zero order) value = tower_zero order.
Proof. exact (proj2 (tower_zero_absorption order)). Qed.
Lemma tower_conj_neg order : forall value,
 tower_conj order (tower_neg order value) = tower_neg order (tower_conj order value).
Proof.
 induction order as [|order induction_equal]; intro value; [reflexivity|].
 destruct value; simpl. rewrite induction_equal. reflexivity.
Qed.
Lemma tower_conj_add order : forall first second,
 tower_conj order (tower_add order first second) = tower_add order (tower_conj order first) (tower_conj order second).
Proof.
 induction order as [|order induction_equal]; intros first second; [reflexivity|].
 destruct first, second; simpl. rewrite induction_equal, tower_neg_add. reflexivity.
Qed.
Lemma tower_conj_involution order : forall value, tower_conj order (tower_conj order value) = value.
Proof.
 induction order as [|order induction_equal]; intro value; [reflexivity|].
 destruct value; simpl. rewrite induction_equal, tower_neg_involution. reflexivity.
Qed.
Lemma tower_mul_neg_laws order :
 (forall first second, tower_mul order (tower_neg order first) second = tower_neg order (tower_mul order first second)) /\
 (forall first second, tower_mul order first (tower_neg order second) = tower_neg order (tower_mul order first second)).
Proof.
 induction order as [|order [neg_left neg_right]].
 - split; intros first second; simpl; ring.
 - split; intros [first_low first_high] [second_low second_high]; simpl; unfold tower_sub;
   repeat rewrite tower_conj_neg; repeat rewrite neg_left; repeat rewrite neg_right;
   repeat rewrite tower_neg_add; repeat rewrite tower_neg_involution; reflexivity.
Qed.
Lemma tower_mul_neg_left order : forall first second,
 tower_mul order (tower_neg order first) second = tower_neg order (tower_mul order first second).
Proof. exact (proj1 (tower_mul_neg_laws order)). Qed.
Lemma tower_mul_neg_right order : forall first second,
 tower_mul order first (tower_neg order second) = tower_neg order (tower_mul order first second).
Proof. exact (proj2 (tower_mul_neg_laws order)). Qed.
Lemma tower_conj_antimorphism order : forall first second,
 tower_conj order (tower_mul order first second) = tower_mul order (tower_conj order second) (tower_conj order first).
Proof.
 induction order as [|order induction_equal]; intros first second.
 - apply Rmult_comm.
 - destruct first as [first_low first_high], second as [second_low second_high].
   simpl; unfold tower_sub.
   repeat rewrite tower_conj_add; repeat rewrite tower_conj_neg;
   repeat rewrite induction_equal; repeat rewrite tower_conj_involution;
   repeat rewrite tower_mul_neg_left; repeat rewrite tower_mul_neg_right;
   repeat rewrite tower_neg_add; repeat rewrite tower_neg_involution.
   f_equal. apply tower_add_comm.
Qed.
Lemma tower_pure_conj_neg order : forall value,
 tower_pure order value -> tower_conj order value = tower_neg order value.
Proof.
 induction order as [|order induction_equal]; intros value pure.
 - unfold tower_pure in pure; simpl in pure; simpl. rewrite pure. ring.
 - destruct value; simpl. f_equal. apply induction_equal. exact pure.
Qed.
Print Assumptions tower_conj_antimorphism.
Print Assumptions tower_pure_conj_neg.
Lemma tower_scale_zero order factor : tower_scale order factor (tower_zero order) = tower_zero order.
Proof. induction order as [|order induction_equal]; simpl; [ring|rewrite induction_equal; reflexivity]. Qed.
Fixpoint tower_norm_sq (order : nat) : cd_tower order -> R :=
 match order as dimension return cd_tower dimension -> R with
 | O => fun value => value^2
 | S lower => fun value => tower_norm_sq lower (fst value) + tower_norm_sq lower (snd value) end.
Lemma tower_norm_neg order : forall value, tower_norm_sq order (tower_neg order value) = tower_norm_sq order value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - simpl; ring.
 - destruct value; simpl. rewrite !induction_equal. reflexivity.
Qed.
Lemma tower_norm_conj order : forall value, tower_norm_sq order (tower_conj order value) = tower_norm_sq order value.
Proof.
 induction order as [|order induction_equal]; intro value; [reflexivity|].
 destruct value; simpl. rewrite induction_equal, tower_norm_neg. reflexivity.
Qed.
Lemma tower_norm_scale order factor : forall value,
 tower_norm_sq order (tower_scale order factor value) = factor^2 * tower_norm_sq order value.
Proof.
 induction order as [|order induction_equal]; intro value.
 - simpl; ring.
 - destruct value; simpl. rewrite !induction_equal. ring.
Qed.
