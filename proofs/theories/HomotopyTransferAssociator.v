(** * Finite Fano incidence counts on octonion basis labels.

    The checked objects are the XOR predicate and the 210 ordered triples
    of distinct labels in {1,...,7}. The theorems count 42 Fano triples and
    168 remaining triples. The file defines neither a retraction polynomial
    nor an A-infinity operation. A transfer interpretation needs a separate
    graded contraction and a proof relating its operations to these counts. *)

From Stdlib Require Import List Arith Bool ZArith Lia.
Import ListNotations.

(** Fano lines as sorted triples. *)
Definition fano_lines : list (nat * nat * nat) :=
  [(1,2,3); (1,4,5); (1,6,7); (2,4,6); (2,5,7); (3,4,7); (3,5,6)].

(** A triple is on a Fano line iff i XOR j XOR k = 0. *)
Definition is_fano_xor (i j k : nat) : bool :=
  Nat.eqb (Nat.lxor (Nat.lxor i j) k) 0.

(** Count Fano-line triples among all 210 ordered triples of {1..7}. *)
Definition fano_triple_count : nat :=
  List.length (List.filter (fun ijk =>
    match ijk with (i, (j, k)) => is_fano_xor i j k end)
    (List.flat_map (fun i =>
      List.flat_map (fun j =>
        if Nat.eqb i j then []
        else List.flat_map (fun k =>
          if orb (Nat.eqb k i) (Nat.eqb k j) then []
          else [(i, (j, k))])
          (List.seq 1 7))
        (List.seq 1 7))
      (List.seq 1 7))).

Theorem fano_triples_are_42 : fano_triple_count = 42.
Proof. vm_compute. reflexivity. Qed.

(** Non-Fano triple count = 210 - 42 = 168. *)
Definition nonfano_triple_count : nat :=
  List.length (List.filter (fun ijk =>
    match ijk with (i, (j, k)) => negb (is_fano_xor i j k) end)
    (List.flat_map (fun i =>
      List.flat_map (fun j =>
        if Nat.eqb i j then []
        else List.flat_map (fun k =>
          if orb (Nat.eqb k i) (Nat.eqb k j) then []
          else [(i, (j, k))])
          (List.seq 1 7))
        (List.seq 1 7))
      (List.seq 1 7))).

Theorem nonfano_triples_are_168 : nonfano_triple_count = 168.
Proof. vm_compute. reflexivity. Qed.

(** Total check: 42 + 168 = 210. *)
Theorem total_triples : fano_triple_count + nonfano_triple_count = 210.
Proof. vm_compute. reflexivity. Qed.

(** Each Fano line has 3! = 6 orderings. 7 * 6 = 42. *)
Theorem fano_lines_times_orderings : 7 * 6 = 42.
Proof. reflexivity. Qed.

Print Assumptions fano_triples_are_42.
Print Assumptions nonfano_triples_are_168.
Print Assumptions total_triples.
Print Assumptions fano_lines_times_orderings.
