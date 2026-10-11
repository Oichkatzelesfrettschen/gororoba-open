(** * Finite octonion sign and associator reflection.

    The recursive sign function computes coefficients of basis products.
    Boolean reflection checks the ordinary associator on all 210 ordered
    distinct triples from {1,...,7}: the 42 XOR-zero triples have zero
    associator, and the other 168 have coefficient +2 or -2.

    The definitions contain no retraction polynomial m3. Equality of such a
    polynomial with the associator requires a separate operation-level
    bridge; these finite sign checks establish no A-infinity structure. *)

From Stdlib Require Import ZArith Bool List Arith.
Import ListNotations.
Open Scope Z_scope.

(** Recursive Cayley-Dickson signs use the highest-bit doubling convention. *)

(** Recursive sign computation matching cd_kernel::cd_basis_mul_sign exactly.

    The recursive cases are:
      dim=1: return 1
      p<half, q<half: recurse(half, p, q)
      p<half, q>=half: recurse(half, q-half, p)  -- NOTE: swaps p and q
      p>=half, q<half: s = recurse(half, p-half, q); if q=0 then s else -s
      p>=half, q>=half: if q-half=0 then -1 else recurse(half, q-half, p-half) *)

Fixpoint cd_sign_fuel (fuel : nat) (dim p q : nat) : Z :=
  match fuel with
  | O => 1%Z  (* base: dim=1 *)
  | S fuel' =>
    let half := Nat.div dim 2 in
    if Nat.eqb half 0 then 1%Z
    else if andb (Nat.ltb p half) (Nat.ltb q half) then
      cd_sign_fuel fuel' half p q
    else if andb (Nat.ltb p half) (negb (Nat.ltb q half)) then
      (* p<half, q>=half: recurse(half, q-half, p) -- swap! *)
      cd_sign_fuel fuel' half (q - half)%nat p
    else if andb (negb (Nat.ltb p half)) (Nat.ltb q half) then
      (* p>=half, q<half: s = recurse(half, p-half, q); negate if q!=0 *)
      let s := cd_sign_fuel fuel' half (p - half)%nat q in
      if Nat.eqb q 0 then s else Z.opp s
    else
      (* both >= half *)
      let qh := (q - half)%nat in
      let ph := (p - half)%nat in
      if Nat.eqb qh 0 then (-1)%Z
      else cd_sign_fuel fuel' half qh ph
  end.

(** Octonion sign: use fuel = 4 (log2(8) + 1), dim = 8. *)
Definition oct_sign (i j : nat) : Z := cd_sign_fuel 4 8 i j.

(** Quick sanity checks matching SedenionAlternativityFails.v *)
Example sign_1_2 : oct_sign 1 2 = 1. Proof. vm_compute. reflexivity. Qed.
Example sign_1_3 : oct_sign 1 3 = (-1). Proof. vm_compute. reflexivity. Qed.
Example sign_2_3 : oct_sign 2 3 = 1. Proof. vm_compute. reflexivity. Qed.
Example sign_self : oct_sign 3 3 = (-1). Proof. vm_compute. reflexivity. Qed.

(** The ordinary associator includes both inner-product signs:
      [e_i,e_j,e_k] = (e_i*e_j)*e_k - e_i*(e_j*e_k)
       = (sign(i,j)*sign(i XOR j,k) - sign(j,k)*sign(i,j XOR k))
         * e_(i XOR j XOR k).
    The coefficient is computed directly from the recursive sign table. *)

Definition assoc_coeff (i j k : nat) : Z :=
  let ij := Nat.lxor i j in
  let jk := Nat.lxor j k in
  oct_sign ij k * oct_sign i j - oct_sign i jk * oct_sign j k.

(** Non-Fano detection via XOR. *)
Definition is_nonfano (i j k : nat) : bool :=
  negb (Nat.eqb (Nat.lxor (Nat.lxor i j) k) 0).

(** Build all 210 ordered triples of distinct elements from {1..7}. *)
Definition all_triples : list (nat * nat * nat) :=
  List.flat_map (fun i =>
    List.flat_map (fun j =>
      if Nat.eqb i j then []
      else List.flat_map (fun k =>
        if orb (Nat.eqb k i) (Nat.eqb k j) then []
        else [(i, j, k)])
        (List.seq 1 7))
      (List.seq 1 7))
    (List.seq 1 7).

(** Associator is nonzero on all 168 non-Fano triples. *)
Definition check_nonfano_nonzero : bool :=
  List.forallb (fun ijk =>
    match ijk with (i, j, k) =>
      if is_nonfano i j k then negb (Z.eqb (assoc_coeff i j k) 0)
      else true
    end) all_triples.

Theorem nonfano_assoc_nonzero : check_nonfano_nonzero = true.
Proof. vm_compute. reflexivity. Qed.

(** Associator is zero on all 42 Fano triples. *)
Definition check_fano_zero : bool :=
  List.forallb (fun ijk =>
    match ijk with (i, j, k) =>
      if negb (is_nonfano i j k) then Z.eqb (assoc_coeff i j k) 0
      else true
    end) all_triples.

Theorem fano_assoc_zero : check_fano_zero = true.
Proof. vm_compute. reflexivity. Qed.

(** Associator magnitude is exactly 2 on all non-Fano triples.
    The ordinary associator is +/-2 * e_{i XOR j XOR k}. *)
Definition check_nonfano_abs2 : bool :=
  List.forallb (fun ijk =>
    match ijk with (i, j, k) =>
      if is_nonfano i j k then
        orb (Z.eqb (assoc_coeff i j k) 2)
            (Z.eqb (assoc_coeff i j k) (-2))
      else true
    end) all_triples.

Theorem nonfano_assoc_is_pm2 : check_nonfano_abs2 = true.
Proof. vm_compute. reflexivity. Qed.

(** Finite associator summary:
    1. Associator = 0 on all 42 Fano-line triples.
    2. Associator != 0 on all 168 non-Fano triples.
    3. |Associator| = 2 on all non-Fano triples.
    All verified by boolean reflection via vm_compute. *)

(** The following finite checks cover the sign table's unit, square,
    anticommutation, XOR-range, and coefficient-magnitude properties. *)

(** All 42 off-diagonal ordered pairs in {1..7} x {1..7}. *)
Definition all_pairs_oct : list (nat * nat) :=
  List.flat_map (fun i =>
    List.flat_map (fun j =>
      if Nat.eqb i j then [] else [(i, j)])
    (List.seq 1 7))
  (List.seq 1 7).

(** Sign anticommutativity: for all distinct i, j in {1..7},
    oct_sign i j + oct_sign j i = 0.
    Equivalently, oct_sign i j = -oct_sign j i. *)
Definition check_sign_anticomm : bool :=
  List.forallb (fun ij =>
    match ij with (i, j) =>
      Z.eqb (oct_sign i j + oct_sign j i) 0
    end) all_pairs_oct.

Theorem sign_anticomm_forallb : check_sign_anticomm = true.
Proof. vm_compute. reflexivity. Qed.

(** Self-square: for all i in {1..7}, oct_sign i i = -1.
    Corresponds to e_i^2 = -e_0 for imaginary basis elements. *)
Definition check_sign_self_neg : bool :=
  List.forallb (fun i => Z.eqb (oct_sign i i) (-1)) (List.seq 1 7).

Theorem sign_self_neg_forallb : check_sign_self_neg = true.
Proof. vm_compute. reflexivity. Qed.

(** Unit element: for all j in {0..7}, oct_sign 0 j = 1.
    Corresponds to e_0 * e_j = e_j (identity element). *)
Definition check_sign_unit_left : bool :=
  List.forallb (fun j => Z.eqb (oct_sign 0 j) 1) (List.seq 0 8).

Theorem sign_unit_left_forallb : check_sign_unit_left = true.
Proof. vm_compute. reflexivity. Qed.

(** Unit element right: for all i in {0..7}, oct_sign i 0 = 1. *)
Definition check_sign_unit_right : bool :=
  List.forallb (fun i => Z.eqb (oct_sign i 0) 1) (List.seq 0 8).

Theorem sign_unit_right_forallb : check_sign_unit_right = true.
Proof. vm_compute. reflexivity. Qed.

(** A conjunction collects four finite sign properties in one reflection. *)

(** XOR index check: for all i, j in {1..7}, i != j,
    the XOR i lxor j is in {1..7} (stays in the imaginary subspace). *)
Definition check_xor_in_range : bool :=
  List.forallb (fun ij =>
    match ij with (i, j) =>
      let xor_ij := Nat.lxor i j in
      andb (Nat.ltb 0 xor_ij) (Nat.ltb xor_ij 8)
    end) all_pairs_oct.

Theorem sign_xor_index_in_range : check_xor_in_range = true.
Proof. vm_compute. reflexivity. Qed.

(** Combo check: anticomm + self_neg + unit_left + xor_in_range.
    Single vm_compute verifies all four sign properties together. *)
Definition check_sign_combo : bool :=
  andb check_sign_anticomm
  (andb check_sign_self_neg
  (andb check_sign_unit_left
        check_xor_in_range)).

Theorem sign_triple_check_combo : check_sign_combo = true.
Proof. vm_compute. reflexivity. Qed.

(** Every coefficient on the 64 basis-index pairs is +1 or -1. *)

(** All 64 pairs in {0..7} x {0..7}. *)
Definition all_pairs_oct_full : list (nat * nat) :=
  List.flat_map (fun i =>
    List.map (fun j => (i, j))
    (List.seq 0 8))
  (List.seq 0 8).

(** Sign magnitude check: forall i j in {0..7},
    oct_sign i j = 1 or oct_sign i j = -1. *)
Definition check_sign_pm1 : bool :=
  List.forallb (fun ij =>
    match ij with (i, j) =>
      orb (Z.eqb (oct_sign i j) 1) (Z.eqb (oct_sign i j) (-1))
    end) all_pairs_oct_full.

Theorem sign_unit_forallb : check_sign_pm1 = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions sign_1_2.
Print Assumptions sign_1_3.
Print Assumptions sign_2_3.
Print Assumptions sign_self.
Print Assumptions nonfano_assoc_nonzero.
Print Assumptions fano_assoc_zero.
Print Assumptions nonfano_assoc_is_pm2.
Print Assumptions sign_anticomm_forallb.
Print Assumptions sign_self_neg_forallb.
Print Assumptions sign_unit_left_forallb.
Print Assumptions sign_unit_right_forallb.
Print Assumptions sign_xor_index_in_range.
Print Assumptions sign_triple_check_combo.
Print Assumptions sign_unit_forallb.
