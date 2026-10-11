(** * Finite associator partition for 32D signs on lower-half labels.

    The input corpus consists of all 2730 ordered distinct triples from
    {1,...,15}. The 32D recursive signs restrict to the sedenion subalgebra
    on these labels and agree with octonion signs on {1,...,7}.

    The checked theorems count 210 XOR-zero triples, prove their associators
    vanish, and prove exhaustiveness of the partition into XOR-zero,
    remaining zero-associator, and nonzero-associator triples. The latter
    two cardinalities are defined but receive no numeric theorem here.

    The file defines no retraction operation. A comparison with a cubic
    retraction polynomial requires a separate operation-level certificate,
    and a transfer interpretation requires a graded contraction. *)

From Stdlib Require Import ZArith Bool List Arith.
Import ListNotations.
Open Scope Z_scope.

(** Import the recursive sign computation from M3IsAssociator. *)
From OpenGororoba Require Import M3IsAssociator.

(** Pathion sign: fuel=6 (log2(32)+1), dim=32. *)
Definition path_sign (i j : nat) : Z := cd_sign_fuel 6 32 i j.

(** Sanity: self-products give -1. *)
Example path_self_1 : path_sign 1 1 = (-1). Proof. vm_compute. reflexivity. Qed.
Example path_self_16 : path_sign 16 16 = (-1). Proof. vm_compute. reflexivity. Qed.
Example path_self_31 : path_sign 31 31 = (-1). Proof. vm_compute. reflexivity. Qed.

(** Products with e_0 give +1. *)
Example path_zero_left : path_sign 0 17 = 1. Proof. vm_compute. reflexivity. Qed.
Example path_zero_right : path_sign 17 0 = 1. Proof. vm_compute. reflexivity. Qed.

(** Pathion associator coefficient using pathion signs. *)
Definition path_assoc_coeff (i j k : nat) : Z :=
  let ij := Nat.lxor i j in
  let jk := Nat.lxor j k in
  path_sign ij k * path_sign i j - path_sign i jk * path_sign j k.

(** Is a triple Fano-like at pathion level?  i XOR j XOR k = 0. *)
Definition is_path_fano (i j k : nat) : bool :=
  Nat.eqb (Nat.lxor (Nat.lxor i j) k) 0.

(** All 15*14*13 = 2730 ordered distinct triples on labels {1,...,15}. *)
Definition sed_triples : list (nat * nat * nat) :=
  List.flat_map (fun i =>
    List.flat_map (fun j =>
      if Nat.eqb i j then []
      else List.flat_map (fun k =>
        if orb (Nat.eqb k i) (Nat.eqb k j) then []
        else [(i, j, k)])
        (List.seq 1 15))
      (List.seq 1 15))
    (List.seq 1 15).

(** Verify that the pathion sign table gives the SAME associator
    classification as the octonion sign table on {1..7} triples.
    This is expected: pathion signs restricted to lower-half indices
    should agree with octonion signs. *)
Definition check_path_oct_agree : bool :=
  List.forallb (fun ijk =>
    match ijk with (i, j, k) =>
      Z.eqb (path_assoc_coeff i j k) (assoc_coeff i j k)
    end)
    all_triples.

Theorem pathion_octonion_sign_agree : check_path_oct_agree = true.
Proof. vm_compute. reflexivity. Qed.

(** Now verify associator properties on {1..15} using PATHION signs.
    The pathion sign table extends the octonion one to 32D. *)

(** Count XOR-zero triples in the declared lower-half corpus. *)
Definition sed_fano_count : nat :=
  List.length (List.filter (fun ijk =>
    match ijk with (i, j, k) => is_path_fano i j k end)
    sed_triples).

(** In {1..15}, the XOR=0 condition identifies MORE triples than the
    7 octonion Fano lines.  The sedenion multiplication table has
    additional XOR-zero triples from the upper-half indices (8..15).
    This count is the number of ordered triples (i,j,k) in {1..15}
    with i != j != k != i and i XOR j XOR k = 0. *)
Theorem sed_fano_count_is : sed_fano_count = 210%nat.
Proof. vm_compute. reflexivity. Qed.

(** On Fano triples of {1..15}: pathion associator is zero. *)
Definition check_sed_fano_zero : bool :=
  List.forallb (fun ijk =>
    match ijk with (i, j, k) =>
      if is_path_fano i j k then Z.eqb (path_assoc_coeff i j k) 0
      else true
    end) sed_triples.

Theorem sed_fano_assoc_zero : check_sed_fano_zero = true.
Proof. vm_compute. reflexivity. Qed.

(** Count triples with nonzero label XOR and zero ordinary associator.
    The predicate concerns the sign-table product alone. *)
Definition sed_nonfano_zero_count : nat :=
  List.length (List.filter (fun ijk =>
    match ijk with (i, j, k) =>
      andb (negb (is_path_fano i j k)) (Z.eqb (path_assoc_coeff i j k) 0)
    end) sed_triples).

Definition sed_nonfano_nonzero_count : nat :=
  List.length (List.filter (fun ijk =>
    match ijk with (i, j, k) =>
      andb (negb (is_path_fano i j k)) (negb (Z.eqb (path_assoc_coeff i j k) 0))
    end) sed_triples).

(** The split: how many non-Fano triples have zero vs nonzero associator
    when using the pathion sign table on {1..15} indices. *)
Definition sed_total_ordered : nat := List.length sed_triples.

Theorem sed_total_is : sed_total_ordered = 2730%nat.
Proof. vm_compute. reflexivity. Qed.

(** Verify: fano + nonfano_zero + nonfano_nonzero = total *)
Theorem sed_partition_complete :
  (sed_fano_count + sed_nonfano_zero_count + sed_nonfano_nonzero_count)%nat
  = sed_total_ordered.
Proof. vm_compute. reflexivity. Qed.

(** The partition is exhaustive on the declared corpus. The theorem above
    leaves both non-Fano class cardinalities as computed definitions and
    supplies no retraction-polynomial or all-dimension conclusion. *)

Print Assumptions path_self_1.
Print Assumptions path_self_16.
Print Assumptions path_self_31.
Print Assumptions path_zero_left.
Print Assumptions path_zero_right.
Print Assumptions pathion_octonion_sign_agree.
Print Assumptions sed_fano_count_is.
Print Assumptions sed_fano_assoc_zero.
Print Assumptions sed_total_is.
Print Assumptions sed_partition_complete.
