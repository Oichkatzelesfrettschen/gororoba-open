(** The recursive real tower as a model of the Moreno interfaces.

    TowerMoreno instantiates CDAlgMorenoSwap at an arbitrary order of the
    recursive tower: the adjoint identities are
    CDTowerKernelSwap.tower_inner_adjoint (Moreno 1997, Lemma 1.3), the
    inner product is the coordinate form, non-degeneracy is its positive
    definiteness, and the two zero-product swap obligations are
    CDTowerKernelSwap.tower_kernel_swap.  MorSkewSymm and MorKernelEquality
    on that model give Proposition 1.7 and the Remark that follows it,
    Ker(L_x) = Ker(R_x) for purely imaginary x, at the chosen order.

    Sedenions and Pathions fix orders 4 (16D) and 5 (32D).  The statement
    for every order at once, with no purity hypothesis, is
    CDTowerKernelSwap.tower_kernel_equality. *)

From Stdlib Require Import Reals.
From OpenGororoba Require Import RecursiveCDTower CDTowerKernelSwap C1539_MorSkewSymm.
Local Open Scope R_scope.

Module Type TowerOrder.
  Parameter order : nat.
End TowerOrder.

Module TowerMoreno (Level : TowerOrder) <: CDAlgMorenoSwap.
  Definition A     := cd_tower Level.order.
  Definition mul   := tower_mul Level.order.
  Definition conj  := tower_conj Level.order.
  Definition neg   := tower_neg Level.order.
  Definition inner := tower_inner Level.order.
  Definition zero  := tower_zero Level.order.

  Lemma inner_adj_left : forall x y z,
    inner (mul x y) z = inner y (mul (conj x) z).
  Proof. exact (tower_inner_adjoint_left Level.order). Qed.

  Lemma inner_adj_right : forall x y z,
    inner (mul x y) z = inner x (mul z (conj y)).
  Proof. exact (tower_inner_adjoint_right Level.order). Qed.

  Lemma inner_symm : forall x y, inner x y = inner y x.
  Proof. exact (tower_inner_symmetric Level.order). Qed.

  Lemma inner_neg_left : forall x y, inner (neg x) y = - inner x y.
  Proof. exact (tower_inner_neg_left Level.order). Qed.

  Lemma inner_neg_right : forall x y, inner x (neg y) = - inner x y.
  Proof. exact (tower_inner_neg_right Level.order). Qed.

  Lemma inner_zero_left : forall y, inner zero y = 0.
  Proof. exact (tower_inner_zero_left Level.order). Qed.

  Lemma neg_mul_left : forall x y, mul (neg x) y = neg (mul x y).
  Proof. exact (tower_mul_neg_left Level.order). Qed.

  Lemma neg_mul_right : forall x y, mul x (neg y) = neg (mul x y).
  Proof. exact (tower_mul_neg_right Level.order). Qed.

  Lemma neg_zero : neg zero = zero.
  Proof. exact (tower_neg_zero Level.order). Qed.

  Lemma inner_nondeg : forall x, (forall y, inner x y = 0) -> x = zero.
  Proof. intros x orthogonal. apply tower_inner_self_zero. apply orthogonal. Qed.

  Lemma pure_left_zero_swap : forall x y,
    conj x = neg x -> mul x y = zero -> mul y x = zero.
  Proof. intros x y _. exact (tower_kernel_swap Level.order x y). Qed.

  Lemma pure_right_zero_swap : forall x y,
    conj x = neg x -> mul y x = zero -> mul x y = zero.
  Proof. intros x y _. exact (tower_kernel_swap Level.order y x). Qed.
End TowerMoreno.

Module SedenionOrder <: TowerOrder.
  Definition order := 4%nat.
End SedenionOrder.

Module PathionOrder <: TowerOrder.
  Definition order := 5%nat.
End PathionOrder.

Module SedenionTowerMoreno := TowerMoreno SedenionOrder.
Module SedenionTowerKernel := MorKernelEquality SedenionTowerMoreno.
Module PathionTowerMoreno := TowerMoreno PathionOrder.
Module PathionTowerKernel := MorKernelEquality PathionTowerMoreno.

(** Proposition 1.7 and the Remark that follows it at 32D (pathions). *)
Theorem pathion_l_x_skew_symm : forall x y z : cd_tower 5,
  tower_conj 5 x = tower_neg 5 x ->
  tower_inner 5 (tower_mul 5 x y) z = - tower_inner 5 y (tower_mul 5 x z).
Proof. exact PathionTowerKernel.Skew.l_x_skew_symm. Qed.

Theorem pathion_ker_lx_eq_ker_rx : forall x y : cd_tower 5,
  tower_conj 5 x = tower_neg 5 x ->
  (tower_mul 5 x y = tower_zero 5 <-> tower_mul 5 y x = tower_zero 5).
Proof. exact PathionTowerKernel.ker_lx_eq_ker_rx. Qed.

Print Assumptions pathion_l_x_skew_symm.
Print Assumptions pathion_ker_lx_eq_ker_rx.
