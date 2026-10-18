(** Highest-bit tower basis products realize the Boolean Schreier sign law.
    Boolean true denotes multiplication by minus one. *)
From Stdlib Require Import Reals Bool.
From OpenGororoba Require Import RecursiveCDTower SchreierSignCode.
Definition tower_signed order (negative : bool) (value : cd_tower order) :=
 if negative then tower_neg order value else value.
Fixpoint tower_basis order : cube order -> cd_tower order :=
 match order as dimension return cube dimension -> cd_tower dimension with
 | O => fun _ => 1%R
 | S lower => fun value => if snd value
   then (tower_basis lower (fst value),tower_zero lower)
   else (tower_basis lower (fst value),tower_zero lower) end.
Lemma tower_signed_zero order negative :
 tower_signed order negative (tower_zero order) = tower_zero order.
Proof. destruct negative; simpl; [apply tower_neg_zero|reflexivity]. Qed.
Lemma tower_signed_composition order first second value :
 tower_signed order first (tower_signed order second value) =
 tower_signed order (xorb first second) value.
Proof. destruct first, second; simpl; try reflexivity; apply tower_neg_involution. Qed.
Lemma tower_signed_mul_left order negative first second :
 tower_mul order (tower_signed order negative first) second =
 tower_signed order negative (tower_mul order first second).
Proof. destruct negative; simpl; [apply tower_mul_neg_left|reflexivity]. Qed.
Lemma tower_signed_mul_right order negative first second :
 tower_mul order first (tower_signed order negative second) =
 tower_signed order negative (tower_mul order first second).
Proof. destruct negative; simpl; [apply tower_mul_neg_right|reflexivity]. Qed.
Lemma tower_signed_low order negative value :
 tower_signed (S order) negative (value,tower_zero order) =
 (tower_signed order negative value,tower_zero order).
Proof. destruct negative; simpl; [rewrite tower_neg_zero|]; reflexivity. Qed.
Lemma tower_signed_high order negative value :
 tower_signed (S order) negative (tower_zero order,value) =
 (tower_zero order,tower_signed order negative value).
Proof. destruct negative; simpl; [rewrite tower_neg_zero|]; reflexivity. Qed.
Theorem tower_basis_conjugation order : forall value,
 tower_conj order (tower_basis order value) =
 tower_signed order (cube_nonzero order value) (tower_basis order value).
Proof.
 induction order as [|order induction_equal]; intro value.
 - destruct value; reflexivity.
 - destruct value as [value high]. rewrite cube_nonzero_double.
   destruct high.
   + rewrite orb_true_r. simpl. rewrite tower_conj_zero, tower_neg_zero. reflexivity.
   + rewrite orb_false_r. cbn [tower_basis tower_conj fst snd].
     rewrite induction_equal, tower_neg_zero, tower_signed_low. reflexivity.
Qed.
Theorem tower_basis_multiplication order : forall first second,
 tower_mul order (tower_basis order first) (tower_basis order second) =
 tower_signed order (sign_exponent order first second)
   (tower_basis order (cube_xor order first second)).
Proof.
 induction order as [|order induction_equal]; intros first second.
 - destruct first, second. simpl. ring.
 - destruct first as [first first_high], second as [second second_high].
   destruct first_high, second_high;
   cbn [tower_basis tower_mul cube_xor sign_exponent fst snd];
   unfold tower_sub;
   repeat rewrite tower_conj_zero;
   repeat rewrite tower_mul_zero_left;
   repeat rewrite tower_mul_zero_right;
   repeat rewrite tower_neg_zero;
   repeat rewrite tower_add_zero;
   repeat rewrite (tower_add_comm order _ (tower_zero order));
   repeat rewrite tower_add_zero;
   rewrite ?tower_basis_conjugation, ?tower_signed_mul_left, ?tower_signed_mul_right;
   rewrite ?induction_equal; cbn [xorb andb].
   + rewrite tower_signed_low, cube_xor_commutative.
     destruct (sign_exponent order second first), (cube_nonzero order second);
       cbn [tower_signed xorb]; rewrite ?tower_neg_involution; reflexivity.
   + rewrite tower_signed_high, tower_signed_composition.
     destruct (sign_exponent order first second), (cube_nonzero order second); reflexivity.
   + rewrite tower_signed_high, xorb_false_r, cube_xor_commutative. reflexivity.
   + rewrite tower_signed_low, xorb_false_r. reflexivity.
Qed.
Print Assumptions tower_basis_conjugation.
Print Assumptions tower_basis_multiplication.
