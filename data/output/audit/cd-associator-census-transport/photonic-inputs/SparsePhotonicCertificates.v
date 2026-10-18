(** Retained photonic sign blocks; Rocq checks every witness equation. *)
From Stdlib Require Import List ZArith.
From OpenGororoba Require Import M3IsAssociator CDSignNumericCorrespondence CDAssociatorDoubling.
Import ListNotations.
Local Open Scope Z_scope.
Definition photonic_witness_block (w : nat * nat * Z * nat * nat * Z) : list Z :=
  let '(i,j,s,k,l,_) := w in
  [M3IsAssociator.cd_sign_fuel 4 16 i k; s * M3IsAssociator.cd_sign_fuel 4 16 j l;
   s * M3IsAssociator.cd_sign_fuel 4 16 j k; M3IsAssociator.cd_sign_fuel 4 16 i l].
Definition retained_sparse_witness_0 := (2%nat,11%nat,1,3%nat,10%nat,1).
Example retained_sparse_block_0 : photonic_witness_block retained_sparse_witness_0 = [1; 1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_1 := (2%nat,11%nat,1,3%nat,10%nat,-1).
Example retained_sparse_block_1 : photonic_witness_block retained_sparse_witness_1 = [1; 1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_2 := (2%nat,11%nat,-1,3%nat,10%nat,1).
Example retained_sparse_block_2 : photonic_witness_block retained_sparse_witness_2 = [1; -1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_3 := (2%nat,11%nat,-1,3%nat,10%nat,-1).
Example retained_sparse_block_3 : photonic_witness_block retained_sparse_witness_3 = [1; -1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_4 := (2%nat,11%nat,1,4%nat,13%nat,1).
Example retained_sparse_block_4 : photonic_witness_block retained_sparse_witness_4 = [1; 1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_5 := (2%nat,11%nat,1,4%nat,13%nat,-1).
Example retained_sparse_block_5 : photonic_witness_block retained_sparse_witness_5 = [1; 1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_6 := (2%nat,11%nat,-1,4%nat,13%nat,1).
Example retained_sparse_block_6 : photonic_witness_block retained_sparse_witness_6 = [1; -1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_7 := (2%nat,11%nat,-1,4%nat,13%nat,-1).
Example retained_sparse_block_7 : photonic_witness_block retained_sparse_witness_7 = [1; -1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_8 := (2%nat,11%nat,1,6%nat,15%nat,1).
Example retained_sparse_block_8 : photonic_witness_block retained_sparse_witness_8 = [-1; 1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_9 := (2%nat,11%nat,1,6%nat,15%nat,-1).
Example retained_sparse_block_9 : photonic_witness_block retained_sparse_witness_9 = [-1; 1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_10 := (2%nat,11%nat,-1,6%nat,15%nat,1).
Example retained_sparse_block_10 : photonic_witness_block retained_sparse_witness_10 = [-1; -1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_11 := (2%nat,11%nat,-1,6%nat,15%nat,-1).
Example retained_sparse_block_11 : photonic_witness_block retained_sparse_witness_11 = [-1; -1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_12 := (3%nat,10%nat,1,2%nat,11%nat,1).
Example retained_sparse_block_12 : photonic_witness_block retained_sparse_witness_12 = [-1; -1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_13 := (3%nat,10%nat,1,2%nat,11%nat,-1).
Example retained_sparse_block_13 : photonic_witness_block retained_sparse_witness_13 = [-1; -1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_14 := (3%nat,10%nat,-1,2%nat,11%nat,1).
Example retained_sparse_block_14 : photonic_witness_block retained_sparse_witness_14 = [-1; 1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_15 := (3%nat,10%nat,-1,2%nat,11%nat,-1).
Example retained_sparse_block_15 : photonic_witness_block retained_sparse_witness_15 = [-1; 1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_16 := (3%nat,10%nat,1,4%nat,13%nat,1).
Example retained_sparse_block_16 : photonic_witness_block retained_sparse_witness_16 = [1; -1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_17 := (3%nat,10%nat,1,4%nat,13%nat,-1).
Example retained_sparse_block_17 : photonic_witness_block retained_sparse_witness_17 = [1; -1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_18 := (3%nat,10%nat,-1,4%nat,13%nat,1).
Example retained_sparse_block_18 : photonic_witness_block retained_sparse_witness_18 = [1; 1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_19 := (3%nat,10%nat,-1,4%nat,13%nat,-1).
Example retained_sparse_block_19 : photonic_witness_block retained_sparse_witness_19 = [1; 1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_20 := (3%nat,10%nat,1,5%nat,12%nat,1).
Example retained_sparse_block_20 : photonic_witness_block retained_sparse_witness_20 = [-1; -1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_21 := (3%nat,10%nat,1,5%nat,12%nat,-1).
Example retained_sparse_block_21 : photonic_witness_block retained_sparse_witness_21 = [-1; -1; -1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_22 := (3%nat,10%nat,-1,5%nat,12%nat,1).
Example retained_sparse_block_22 : photonic_witness_block retained_sparse_witness_22 = [-1; 1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_23 := (3%nat,10%nat,-1,5%nat,12%nat,-1).
Example retained_sparse_block_23 : photonic_witness_block retained_sparse_witness_23 = [-1; 1; 1; -1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_24 := (1%nat,9%nat,1,3%nat,11%nat,1).
Example retained_sparse_block_24 : photonic_witness_block retained_sparse_witness_24 = [-1; 1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_25 := (1%nat,9%nat,1,3%nat,11%nat,-1).
Example retained_sparse_block_25 : photonic_witness_block retained_sparse_witness_25 = [-1; 1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_26 := (1%nat,9%nat,-1,3%nat,11%nat,1).
Example retained_sparse_block_26 : photonic_witness_block retained_sparse_witness_26 = [-1; -1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_27 := (1%nat,9%nat,-1,3%nat,11%nat,-1).
Example retained_sparse_block_27 : photonic_witness_block retained_sparse_witness_27 = [-1; -1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_28 := (2%nat,3%nat,-1,4%nat,5%nat,1).
Example retained_sparse_block_28 : photonic_witness_block retained_sparse_witness_28 = [1; 1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_29 := (2%nat,3%nat,-1,4%nat,5%nat,-1).
Example retained_sparse_block_29 : photonic_witness_block retained_sparse_witness_29 = [1; 1; -1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_30 := (2%nat,3%nat,1,4%nat,5%nat,1).
Example retained_sparse_block_30 : photonic_witness_block retained_sparse_witness_30 = [1; -1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_witness_31 := (2%nat,3%nat,1,4%nat,5%nat,-1).
Example retained_sparse_block_31 : photonic_witness_block retained_sparse_witness_31 = [1; -1; 1; 1].
Proof. vm_compute. reflexivity. Qed.
Definition retained_sparse_configurations : list (list Z * Z) := [
([1; 1; 1; -1],1);
([1; 1; 1; -1],-1);
([1; -1; -1; -1],1);
([1; -1; -1; -1],-1);
([1; 1; -1; -1],1);
([1; 1; -1; -1],-1);
([1; -1; 1; -1],1);
([1; -1; 1; -1],-1);
([-1; 1; -1; 1],1);
([-1; 1; -1; 1],-1);
([-1; -1; 1; 1],1);
([-1; -1; 1; 1],-1);
([-1; -1; 1; -1],1);
([-1; -1; 1; -1],-1);
([-1; 1; -1; -1],1);
([-1; 1; -1; -1],-1);
([1; -1; -1; 1],1);
([1; -1; -1; 1],-1);
([1; 1; 1; 1],1);
([1; 1; 1; 1],-1);
([-1; -1; -1; -1],1);
([-1; -1; -1; -1],-1);
([-1; 1; 1; -1],1);
([-1; 1; 1; -1],-1);
([-1; 1; 1; 1],1);
([-1; 1; 1; 1],-1);
([-1; -1; -1; 1],1);
([-1; -1; -1; 1],-1);
([1; 1; -1; 1],1);
([1; 1; -1; 1],-1);
([1; -1; 1; 1],1);
([1; -1; 1; 1],-1)
].
Theorem retained_sparse_configuration_coverage : forall first second third fourth partner : bool,
  In ([phase_sign first; phase_sign second; phase_sign third; phase_sign fourth], phase_sign partner) retained_sparse_configurations.
Proof. intros [] [] [] [] []; vm_compute; tauto. Qed.
Print Assumptions retained_sparse_configuration_coverage.
Definition retained_sparse_witnesses : list (nat * nat * Z * nat * nat * Z) := [
(2%nat,11%nat,1,3%nat,10%nat,1);
(2%nat,11%nat,1,3%nat,10%nat,-1);
(2%nat,11%nat,-1,3%nat,10%nat,1);
(2%nat,11%nat,-1,3%nat,10%nat,-1);
(2%nat,11%nat,1,4%nat,13%nat,1);
(2%nat,11%nat,1,4%nat,13%nat,-1);
(2%nat,11%nat,-1,4%nat,13%nat,1);
(2%nat,11%nat,-1,4%nat,13%nat,-1);
(2%nat,11%nat,1,6%nat,15%nat,1);
(2%nat,11%nat,1,6%nat,15%nat,-1);
(2%nat,11%nat,-1,6%nat,15%nat,1);
(2%nat,11%nat,-1,6%nat,15%nat,-1);
(3%nat,10%nat,1,2%nat,11%nat,1);
(3%nat,10%nat,1,2%nat,11%nat,-1);
(3%nat,10%nat,-1,2%nat,11%nat,1);
(3%nat,10%nat,-1,2%nat,11%nat,-1);
(3%nat,10%nat,1,4%nat,13%nat,1);
(3%nat,10%nat,1,4%nat,13%nat,-1);
(3%nat,10%nat,-1,4%nat,13%nat,1);
(3%nat,10%nat,-1,4%nat,13%nat,-1);
(3%nat,10%nat,1,5%nat,12%nat,1);
(3%nat,10%nat,1,5%nat,12%nat,-1);
(3%nat,10%nat,-1,5%nat,12%nat,1);
(3%nat,10%nat,-1,5%nat,12%nat,-1);
(1%nat,9%nat,1,3%nat,11%nat,1);
(1%nat,9%nat,1,3%nat,11%nat,-1);
(1%nat,9%nat,-1,3%nat,11%nat,1);
(1%nat,9%nat,-1,3%nat,11%nat,-1);
(2%nat,3%nat,-1,4%nat,5%nat,1);
(2%nat,3%nat,-1,4%nat,5%nat,-1);
(2%nat,3%nat,1,4%nat,5%nat,1);
(2%nat,3%nat,1,4%nat,5%nat,-1)
].
Definition photonic_witness_configuration (w : nat * nat * Z * nat * nat * Z) :=
  let '(_,_,_,_,_,t) := w in (photonic_witness_block w,t).
Theorem retained_sparse_witness_map : map photonic_witness_configuration retained_sparse_witnesses = retained_sparse_configurations.
Proof. vm_compute. reflexivity. Qed.
Theorem retained_sparse_witness_total : forall configuration, In configuration retained_sparse_configurations ->
  exists witness, In witness retained_sparse_witnesses /\ photonic_witness_configuration witness = configuration.
Proof. intros configuration member. rewrite <- retained_sparse_witness_map in member.
  apply in_map_iff in member. destruct member as [witness [equation member]]. exists witness. auto. Qed.
Print Assumptions retained_sparse_witness_map.
Print Assumptions retained_sparse_witness_total.
Definition photonic_witness_domain (w : nat * nat * Z * nat * nat * Z) : bool :=
  let '(i,j,s,k,l,t) := w in
  andb (andb (andb (Nat.ltb 0 i) (Nat.ltb i 16)) (andb (Nat.ltb 0 j) (Nat.ltb j 16)))
    (andb (andb (andb (Nat.ltb 0 k) (Nat.ltb k 16)) (andb (Nat.ltb 0 l) (Nat.ltb l 16)))
      (andb (andb (negb (Nat.eqb i j)) (negb (Nat.eqb k l)))
        (andb (Nat.eqb (Nat.lxor i j) (Nat.lxor k l))
          (andb (orb (Z.eqb s 1) (Z.eqb s (-1))) (orb (Z.eqb t 1) (Z.eqb t (-1))))))).
Theorem retained_sparse_witness_domains : Forall (fun witness => photonic_witness_domain witness = true) retained_sparse_witnesses.
Proof. vm_compute. repeat constructor. Qed.
Print Assumptions retained_sparse_witness_domains.
