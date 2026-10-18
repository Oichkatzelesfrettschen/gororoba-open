(** Concrete records preserve the recursive tower's ordered low/high coordinates. *)
From OpenGororoba Require Import Prelude CayleyDicksonAlgebra Sedenion OctonionNorm RecursiveCDTower.
Definition tower_quaternion (value : cd_tower 2) : CDQuat :=
 mkQuat (fst (fst value)) (snd (fst value)) (fst (snd value)) (snd (snd value)).
Definition quaternion_tower (value : CDQuat) : cd_tower 2 := ((qa value,qb value),(qc value,qd value)).
Definition tower_octonion (value : cd_tower 3) : CDOct :=
 mkOct (tower_quaternion (fst value)) (tower_quaternion (snd value)).
Definition octonion_tower (value : CDOct) : cd_tower 3 :=
 (quaternion_tower (oct_lo value),quaternion_tower (oct_hi value)).
Definition tower_sedenion (value : cd_tower 4) : CDSed :=
 mkSed (tower_octonion (fst value)) (tower_octonion (snd value)).
Definition sedenion_tower (value : CDSed) : cd_tower 4 :=
 (octonion_tower (sed_lo value),octonion_tower (sed_hi value)).
Lemma quaternion_tower_round_trip value : quaternion_tower (tower_quaternion value) = value.
Proof. destruct value as [[a b] [c d]]; reflexivity. Qed.
Lemma tower_quaternion_round_trip value : tower_quaternion (quaternion_tower value) = value.
Proof. destruct value; reflexivity. Qed.
Lemma octonion_tower_round_trip value : octonion_tower (tower_octonion value) = value.
Proof. destruct value; unfold octonion_tower, tower_octonion; simpl. rewrite !quaternion_tower_round_trip; reflexivity. Qed.
Lemma tower_octonion_round_trip value : tower_octonion (octonion_tower value) = value.
Proof. destruct value; unfold octonion_tower, tower_octonion; simpl. rewrite !tower_quaternion_round_trip; reflexivity. Qed.
Lemma sedenion_tower_round_trip value : sedenion_tower (tower_sedenion value) = value.
Proof. destruct value; unfold sedenion_tower, tower_sedenion; simpl. rewrite !octonion_tower_round_trip; reflexivity. Qed.
Lemma tower_sedenion_round_trip value : tower_sedenion (sedenion_tower value) = value.
Proof. destruct value; unfold sedenion_tower, tower_sedenion; simpl. rewrite !tower_octonion_round_trip; reflexivity. Qed.
Lemma tower_quaternion_zero : tower_quaternion (tower_zero 2) = quat_zero.
Proof. reflexivity. Qed.
Lemma tower_quaternion_add first second :
 tower_quaternion (tower_add 2 first second) = quat_add (tower_quaternion first) (tower_quaternion second).
Proof. destruct first as [[a b] [c d]], second as [[e f] [g h]]; reflexivity. Qed.
Lemma tower_quaternion_neg value : tower_quaternion (tower_neg 2 value) = quat_neg (tower_quaternion value).
Proof. destruct value as [[a b] [c d]]; reflexivity. Qed.
Lemma tower_quaternion_scale factor value :
 tower_quaternion (tower_scale 2 factor value) = quat_scale factor (tower_quaternion value).
Proof. destruct value as [[a b] [c d]]; reflexivity. Qed.
Lemma tower_quaternion_conj value : tower_quaternion (tower_conj 2 value) = quat_conj (tower_quaternion value).
Proof. destruct value as [[a b] [c d]]; reflexivity. Qed.
Lemma tower_quaternion_mul first second :
 tower_quaternion (tower_mul 2 first second) = quat_mul (tower_quaternion first) (tower_quaternion second).
Proof.
 destruct first as [[a b] [c d]], second as [[e f] [g h]].
 cbv [tower_quaternion tower_mul tower_sub tower_add tower_neg tower_conj quat_mul qa qb qc qd fst snd].
 f_equal; ring.
Qed.
Lemma tower_octonion_zero : tower_octonion (tower_zero 3) = oct_zero.
Proof. reflexivity. Qed.
Lemma tower_octonion_add first second :
 tower_octonion (tower_add 3 first second) = oct_add (tower_octonion first) (tower_octonion second).
Proof. destruct first as [[[a b] [c d]] [[e f] [g h]]], second as [[[i j] [k l]] [[m n] [p q]]]; reflexivity. Qed.
Lemma tower_octonion_neg value : tower_octonion (tower_neg 3 value) = oct_neg (tower_octonion value).
Proof. destruct value as [[[a b] [c d]] [[e f] [g h]]]; reflexivity. Qed.
Lemma tower_octonion_scale factor value :
 tower_octonion (tower_scale 3 factor value) = oct_scale factor (tower_octonion value).
Proof. destruct value as [[[a b] [c d]] [[e f] [g h]]]; reflexivity. Qed.
Lemma tower_octonion_conj value : tower_octonion (tower_conj 3 value) = oct_conj (tower_octonion value).
Proof. destruct value as [[[a b] [c d]] [[e f] [g h]]]; reflexivity. Qed.
Lemma tower_octonion_mul first second :
 tower_octonion (tower_mul 3 first second) = oct_mul (tower_octonion first) (tower_octonion second).
Proof.
 destruct first as [[[a b] [c d]] [[e f] [g h]]], second as [[[i j] [k l]] [[m n] [p q]]].
 cbv [tower_octonion tower_quaternion tower_mul tower_sub tower_add tower_neg tower_conj oct_mul quat_mul quat_add quat_neg quat_conj oct_lo oct_hi qa qb qc qd fst snd].
 f_equal; f_equal; ring.
Qed.
Lemma tower_sedenion_zero : tower_sedenion (tower_zero 4) = sed_zero.
Proof. reflexivity. Qed.
Lemma tower_sedenion_add first second :
 tower_sedenion (tower_add 4 first second) = sed_add (tower_sedenion first) (tower_sedenion second).
Proof.
 destruct first as [[[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]] [[[a8 a9] [a10 a11]] [[a12 a13] [a14 a15]]]],
 second as [[[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]] [[[b8 b9] [b10 b11]] [[b12 b13] [b14 b15]]]]; reflexivity.
Qed.
Lemma tower_sedenion_neg value : tower_sedenion (tower_neg 4 value) = sed_neg (tower_sedenion value).
Proof.
 destruct value as [[[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]] [[[a8 a9] [a10 a11]] [[a12 a13] [a14 a15]]]]; reflexivity.
Qed.
Lemma tower_sedenion_scale factor value :
 tower_sedenion (tower_scale 4 factor value) = sed_scale factor (tower_sedenion value).
Proof.
 destruct value as [[[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]] [[[a8 a9] [a10 a11]] [[a12 a13] [a14 a15]]]]; reflexivity.
Qed.
Lemma tower_sedenion_conj value : tower_sedenion (tower_conj 4 value) = sed_conj (tower_sedenion value).
Proof.
 destruct value as [[[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]] [[[a8 a9] [a10 a11]] [[a12 a13] [a14 a15]]]]; reflexivity.
Qed.
Lemma tower_sedenion_mul first second :
 tower_sedenion (tower_mul 4 first second) = sed_mul (tower_sedenion first) (tower_sedenion second).
Proof.
 destruct first as [[[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]] [[[a8 a9] [a10 a11]] [[a12 a13] [a14 a15]]]],
 second as [[[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]] [[[b8 b9] [b10 b11]] [[b12 b13] [b14 b15]]]].
 cbv [tower_sedenion tower_octonion tower_quaternion tower_mul tower_sub tower_add tower_neg tower_conj sed_mul oct_mul oct_add oct_neg oct_conj quat_mul quat_add quat_neg quat_conj sed_lo sed_hi oct_lo oct_hi qa qb qc qd fst snd].
 f_equal; f_equal; f_equal; ring.
Qed.
Print Assumptions tower_quaternion_mul.
Print Assumptions tower_octonion_mul.
Print Assumptions tower_sedenion_mul.
Lemma tower_sedenion_injective first second : tower_sedenion first = tower_sedenion second -> first = second.
Proof.
 intro equal. apply (f_equal sedenion_tower) in equal.
 rewrite !sedenion_tower_round_trip in equal. exact equal.
Qed.
Lemma tower_quaternion_norm value : tower_norm_sq 2 value = quat_norm_sq (tower_quaternion value).
Proof.
 destruct value as [[a b] [c d]].
 cbv [tower_norm_sq tower_quaternion quat_norm_sq qa qb qc qd fst snd]; ring.
Qed.
Lemma tower_octonion_norm value : tower_norm_sq 3 value = oct_norm_sq (tower_octonion value).
Proof.
 destruct value; change (tower_norm_sq 2 c + tower_norm_sq 2 c0 = quat_norm_sq (tower_quaternion c) + quat_norm_sq (tower_quaternion c0)).
 rewrite !tower_quaternion_norm. reflexivity.
Qed.
Lemma tower_sedenion_norm value : tower_norm_sq 4 value = sed_norm_sq (tower_sedenion value).
Proof.
 destruct value; change (tower_norm_sq 3 c + tower_norm_sq 3 c0 = oct_norm_sq (tower_octonion c) + oct_norm_sq (tower_octonion c0)).
 rewrite !tower_octonion_norm. reflexivity.
Qed.
Print Assumptions tower_sedenion_norm.
