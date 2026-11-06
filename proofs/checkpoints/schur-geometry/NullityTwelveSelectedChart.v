(** Exact selected-center chart identities; candidates require kernel checking. *)
From Stdlib Require Import Reals Arith Bool.
From mathcomp Require boot order algebra.
From OpenGororoba Require Import FiniteMatrixConventions ExactRankCertificate CDSparseMatrixTransport CDSignNumericCorrespondence RationalRealSpecialization RecursiveCDTower CDTowerMatrixAdapter.
From OpenGororobaCheckpoint Require Import RationalMatrixEquationChecker CDTowerOperatorCorrespondence.
Import ssreflect ssrbool matrix mxalgebra rat fintype divalg.
Import -(coercions) rings_modules_and_algebras divalg.
Import divalg.
Import GRing.Theory.
Local Open Scope ring_scope.
Definition chart_center_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.ratz (ssrint.Negz 0))
  | 0%nat,18%nat => (rat.ratz (ssrint.Negz 0))
  | 1%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 1%nat,19%nat => (rat.ratz (ssrint.Negz 0))
  | 2%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 2%nat,16%nat => (rat.ratz (ssrint.Negz 0))
  | 3%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 3%nat,17%nat => (rat.ratz (ssrint.Posz 1))
  | 4%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 4%nat,22%nat => (rat.ratz (ssrint.Posz 1))
  | 5%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 5%nat,23%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,20%nat => (rat.ratz (ssrint.Negz 0))
  | 7%nat,6%nat => (rat.ratz (ssrint.Negz 0))
  | 7%nat,21%nat => (rat.ratz (ssrint.Negz 0))
  | 8%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 8%nat,26%nat => (rat.ratz (ssrint.Posz 1))
  | 9%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 9%nat,27%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,24%nat => (rat.ratz (ssrint.Negz 0))
  | 11%nat,10%nat => (rat.ratz (ssrint.Negz 0))
  | 11%nat,25%nat => (rat.ratz (ssrint.Negz 0))
  | 12%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 12%nat,30%nat => (rat.ratz (ssrint.Negz 0))
  | 13%nat,12%nat => (rat.ratz (ssrint.Negz 0))
  | 13%nat,31%nat => (rat.ratz (ssrint.Negz 0))
  | 14%nat,15%nat => (rat.ratz (ssrint.Negz 0))
  | 14%nat,28%nat => (rat.ratz (ssrint.Posz 1))
  | 15%nat,14%nat => (rat.ratz (ssrint.Posz 1))
  | 15%nat,29%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,17%nat => (rat.ratz (ssrint.Negz 0))
  | 17%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 17%nat,16%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,19%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,1%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,18%nat => (rat.ratz (ssrint.Negz 0))
  | 20%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 20%nat,21%nat => (rat.ratz (ssrint.Posz 1))
  | 21%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 21%nat,20%nat => (rat.ratz (ssrint.Negz 0))
  | 22%nat,4%nat => (rat.ratz (ssrint.Negz 0))
  | 22%nat,23%nat => (rat.ratz (ssrint.Negz 0))
  | 23%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 23%nat,22%nat => (rat.ratz (ssrint.Posz 1))
  | 24%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 24%nat,25%nat => (rat.ratz (ssrint.Posz 1))
  | 25%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 25%nat,24%nat => (rat.ratz (ssrint.Negz 0))
  | 26%nat,8%nat => (rat.ratz (ssrint.Negz 0))
  | 26%nat,27%nat => (rat.ratz (ssrint.Negz 0))
  | 27%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 27%nat,26%nat => (rat.ratz (ssrint.Posz 1))
  | 28%nat,14%nat => (rat.ratz (ssrint.Negz 0))
  | 28%nat,29%nat => (rat.ratz (ssrint.Negz 0))
  | 29%nat,15%nat => (rat.ratz (ssrint.Negz 0))
  | 29%nat,28%nat => (rat.ratz (ssrint.Posz 1))
  | 30%nat,12%nat => (rat.ratz (ssrint.Posz 1))
  | 30%nat,31%nat => (rat.ratz (ssrint.Posz 1))
  | 31%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 31%nat,30%nat => (rat.ratz (ssrint.Negz 0))
  | _,_ => rat.zeroq
  end.
Definition chart_center := rational_data_matrix 32 32 chart_center_data.
Definition chart_complement_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.ratz (ssrint.Negz 0))
  | 0%nat,18%nat => (rat.ratz (ssrint.Negz 0))
  | 1%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 1%nat,19%nat => (rat.ratz (ssrint.Negz 0))
  | 2%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 2%nat,16%nat => (rat.ratz (ssrint.Negz 0))
  | 3%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 3%nat,17%nat => (rat.ratz (ssrint.Posz 1))
  | 4%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 5%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 7%nat,6%nat => (rat.ratz (ssrint.Negz 0))
  | 8%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 9%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 11%nat,10%nat => (rat.ratz (ssrint.Negz 0))
  | 12%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 13%nat,12%nat => (rat.ratz (ssrint.Negz 0))
  | 14%nat,15%nat => (rat.ratz (ssrint.Negz 0))
  | 15%nat,14%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,17%nat => (rat.ratz (ssrint.Negz 0))
  | 17%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 17%nat,16%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,19%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,1%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,18%nat => (rat.ratz (ssrint.Negz 0))
  | 20%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 21%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 22%nat,4%nat => (rat.ratz (ssrint.Negz 0))
  | 23%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 24%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 25%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 26%nat,8%nat => (rat.ratz (ssrint.Negz 0))
  | 27%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 28%nat,14%nat => (rat.ratz (ssrint.Negz 0))
  | 29%nat,15%nat => (rat.ratz (ssrint.Negz 0))
  | 30%nat,12%nat => (rat.ratz (ssrint.Posz 1))
  | 31%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | _,_ => rat.zeroq
  end.
Definition chart_complement := rational_data_matrix 32 20 chart_complement_data.
Definition chart_kernel_data (row column : nat) : rat.rat :=
  match row,column with
  | 4%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 5%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,1%nat => (rat.ratz (ssrint.Negz 0))
  | 7%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 8%nat,7%nat => (rat.ratz (ssrint.Negz 0))
  | 9%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 11%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 12%nat,11%nat => (rat.ratz (ssrint.Negz 0))
  | 13%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 14%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 15%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 20%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 21%nat,1%nat => (rat.ratz (ssrint.Posz 1))
  | 22%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 23%nat,3%nat => (rat.ratz (ssrint.Posz 1))
  | 24%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 25%nat,5%nat => (rat.ratz (ssrint.Posz 1))
  | 26%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 27%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 28%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 29%nat,9%nat => (rat.ratz (ssrint.Posz 1))
  | 30%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 31%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | _,_ => rat.zeroq
  end.
Definition chart_kernel := rational_data_matrix 32 12 chart_kernel_data.
Definition chart_basis_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.ratz (ssrint.Negz 0))
  | 0%nat,18%nat => (rat.ratz (ssrint.Negz 0))
  | 1%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 1%nat,19%nat => (rat.ratz (ssrint.Negz 0))
  | 2%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 2%nat,16%nat => (rat.ratz (ssrint.Negz 0))
  | 3%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 3%nat,17%nat => (rat.ratz (ssrint.Posz 1))
  | 4%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 4%nat,23%nat => (rat.ratz (ssrint.Negz 0))
  | 5%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 5%nat,22%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,21%nat => (rat.ratz (ssrint.Negz 0))
  | 7%nat,6%nat => (rat.ratz (ssrint.Negz 0))
  | 7%nat,20%nat => (rat.ratz (ssrint.Posz 1))
  | 8%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 8%nat,27%nat => (rat.ratz (ssrint.Negz 0))
  | 9%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 9%nat,26%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,25%nat => (rat.ratz (ssrint.Negz 0))
  | 11%nat,10%nat => (rat.ratz (ssrint.Negz 0))
  | 11%nat,24%nat => (rat.ratz (ssrint.Posz 1))
  | 12%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 12%nat,31%nat => (rat.ratz (ssrint.Negz 0))
  | 13%nat,12%nat => (rat.ratz (ssrint.Negz 0))
  | 13%nat,30%nat => (rat.ratz (ssrint.Posz 1))
  | 14%nat,15%nat => (rat.ratz (ssrint.Negz 0))
  | 14%nat,29%nat => (rat.ratz (ssrint.Negz 0))
  | 15%nat,14%nat => (rat.ratz (ssrint.Posz 1))
  | 15%nat,28%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,17%nat => (rat.ratz (ssrint.Negz 0))
  | 17%nat,3%nat => (rat.ratz (ssrint.Negz 0))
  | 17%nat,16%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,19%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,1%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,18%nat => (rat.ratz (ssrint.Negz 0))
  | 20%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 20%nat,20%nat => (rat.ratz (ssrint.Posz 1))
  | 21%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 21%nat,21%nat => (rat.ratz (ssrint.Posz 1))
  | 22%nat,4%nat => (rat.ratz (ssrint.Negz 0))
  | 22%nat,22%nat => (rat.ratz (ssrint.Posz 1))
  | 23%nat,5%nat => (rat.ratz (ssrint.Negz 0))
  | 23%nat,23%nat => (rat.ratz (ssrint.Posz 1))
  | 24%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 24%nat,24%nat => (rat.ratz (ssrint.Posz 1))
  | 25%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 25%nat,25%nat => (rat.ratz (ssrint.Posz 1))
  | 26%nat,8%nat => (rat.ratz (ssrint.Negz 0))
  | 26%nat,26%nat => (rat.ratz (ssrint.Posz 1))
  | 27%nat,9%nat => (rat.ratz (ssrint.Negz 0))
  | 27%nat,27%nat => (rat.ratz (ssrint.Posz 1))
  | 28%nat,14%nat => (rat.ratz (ssrint.Negz 0))
  | 28%nat,28%nat => (rat.ratz (ssrint.Posz 1))
  | 29%nat,15%nat => (rat.ratz (ssrint.Negz 0))
  | 29%nat,29%nat => (rat.ratz (ssrint.Posz 1))
  | 30%nat,12%nat => (rat.ratz (ssrint.Posz 1))
  | 30%nat,30%nat => (rat.ratz (ssrint.Posz 1))
  | 31%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 31%nat,31%nat => (rat.ratz (ssrint.Posz 1))
  | _,_ => rat.zeroq
  end.
Definition chart_basis := rational_data_matrix 32 32 chart_basis_data.
Definition chart_basis_inverse_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 0%nat,18%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 1%nat,0%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 1%nat,19%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 2%nat,3%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 2%nat,16%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 3%nat,2%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 3%nat,17%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 4%nat,5%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 4%nat,22%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 5%nat,4%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 5%nat,23%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 6%nat,7%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 6%nat,20%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 7%nat,6%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 7%nat,21%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 8%nat,9%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 8%nat,26%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 9%nat,8%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 9%nat,27%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 10%nat,11%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 10%nat,24%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 11%nat,10%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 11%nat,25%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 12%nat,13%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 12%nat,30%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 13%nat,12%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 13%nat,31%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 14%nat,15%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 14%nat,28%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 15%nat,14%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 15%nat,29%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 16%nat,2%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 16%nat,17%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 17%nat,3%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 17%nat,16%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 18%nat,0%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 18%nat,19%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 19%nat,1%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 19%nat,18%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 20%nat,7%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 20%nat,20%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 21%nat,6%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 21%nat,21%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 22%nat,5%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 22%nat,22%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 23%nat,4%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 23%nat,23%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 24%nat,11%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 24%nat,24%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 25%nat,10%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 25%nat,25%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 26%nat,9%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 26%nat,26%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 27%nat,8%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 27%nat,27%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 28%nat,15%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 28%nat,28%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 29%nat,14%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 29%nat,29%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 30%nat,13%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 30%nat,30%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 31%nat,12%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 31%nat,31%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | _,_ => rat.zeroq
  end.
Definition chart_basis_inverse := rational_data_matrix 32 32 chart_basis_inverse_data.
Definition chart_decoder_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,7%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 0%nat,20%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 1%nat,6%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 1%nat,21%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 2%nat,5%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 2%nat,22%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 3%nat,4%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 3%nat,23%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 4%nat,11%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 4%nat,24%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 5%nat,10%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 5%nat,25%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 6%nat,9%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 6%nat,26%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 7%nat,8%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 7%nat,27%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 8%nat,15%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 8%nat,28%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 9%nat,14%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 9%nat,29%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 10%nat,13%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 10%nat,30%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 11%nat,12%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 11%nat,31%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | _,_ => rat.zeroq
  end.
Definition chart_decoder := rational_data_matrix 12 32 chart_decoder_data.
Definition chart_pivot_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.ratz (ssrint.Negz 1))
  | 0%nat,18%nat => (rat.ratz (ssrint.Negz 1))
  | 1%nat,0%nat => (rat.ratz (ssrint.Posz 2))
  | 1%nat,19%nat => (rat.ratz (ssrint.Negz 1))
  | 2%nat,3%nat => (rat.ratz (ssrint.Negz 1))
  | 2%nat,16%nat => (rat.ratz (ssrint.Negz 1))
  | 3%nat,2%nat => (rat.ratz (ssrint.Posz 2))
  | 3%nat,17%nat => (rat.ratz (ssrint.Posz 2))
  | 4%nat,5%nat => (rat.ratz (ssrint.Negz 3))
  | 5%nat,4%nat => (rat.ratz (ssrint.Posz 4))
  | 6%nat,7%nat => (rat.ratz (ssrint.Posz 4))
  | 7%nat,6%nat => (rat.ratz (ssrint.Negz 3))
  | 8%nat,9%nat => (rat.ratz (ssrint.Negz 3))
  | 9%nat,8%nat => (rat.ratz (ssrint.Posz 4))
  | 10%nat,11%nat => (rat.ratz (ssrint.Posz 4))
  | 11%nat,10%nat => (rat.ratz (ssrint.Negz 3))
  | 12%nat,13%nat => (rat.ratz (ssrint.Posz 4))
  | 13%nat,12%nat => (rat.ratz (ssrint.Negz 3))
  | 14%nat,15%nat => (rat.ratz (ssrint.Negz 3))
  | 15%nat,14%nat => (rat.ratz (ssrint.Posz 4))
  | 16%nat,2%nat => (rat.ratz (ssrint.Posz 2))
  | 16%nat,17%nat => (rat.ratz (ssrint.Negz 1))
  | 17%nat,3%nat => (rat.ratz (ssrint.Negz 1))
  | 17%nat,16%nat => (rat.ratz (ssrint.Posz 2))
  | 18%nat,0%nat => (rat.ratz (ssrint.Posz 2))
  | 18%nat,19%nat => (rat.ratz (ssrint.Posz 2))
  | 19%nat,1%nat => (rat.ratz (ssrint.Posz 2))
  | 19%nat,18%nat => (rat.ratz (ssrint.Negz 1))
  | _,_ => rat.zeroq
  end.
Definition chart_pivot := rational_data_matrix 20 20 chart_pivot_data.
Definition chart_pivot_inverse_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 0%nat,18%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 1%nat,0%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 1%nat,19%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 2%nat,3%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 2%nat,16%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 3%nat,2%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 3%nat,17%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 4%nat,5%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 5%nat,4%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 6%nat,7%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 7%nat,6%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 8%nat,9%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 9%nat,8%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 10%nat,11%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 11%nat,10%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 12%nat,13%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 13%nat,12%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 14%nat,15%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 15%nat,14%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 16%nat,2%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 16%nat,17%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 17%nat,3%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | 17%nat,16%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 18%nat,0%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 18%nat,19%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 19%nat,1%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 4)))
  | 19%nat,18%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 4)))
  | _,_ => rat.zeroq
  end.
Definition chart_pivot_inverse := rational_data_matrix 20 20 chart_pivot_inverse_data.
Definition chart_upper_right_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 1%nat,1%nat => (rat.ratz (ssrint.Posz 1))
  | 2%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 3%nat,3%nat => (rat.ratz (ssrint.Posz 1))
  | 4%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 4%nat,23%nat => (rat.ratz (ssrint.Posz 1))
  | 5%nat,5%nat => (rat.ratz (ssrint.Posz 1))
  | 5%nat,22%nat => (rat.ratz (ssrint.Negz 0))
  | 6%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,21%nat => (rat.ratz (ssrint.Posz 1))
  | 7%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 7%nat,20%nat => (rat.ratz (ssrint.Negz 0))
  | 8%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 8%nat,27%nat => (rat.ratz (ssrint.Posz 1))
  | 9%nat,9%nat => (rat.ratz (ssrint.Posz 1))
  | 9%nat,26%nat => (rat.ratz (ssrint.Negz 0))
  | 10%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,25%nat => (rat.ratz (ssrint.Posz 1))
  | 11%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 11%nat,24%nat => (rat.ratz (ssrint.Negz 0))
  | 12%nat,12%nat => (rat.ratz (ssrint.Posz 1))
  | 12%nat,31%nat => (rat.ratz (ssrint.Posz 1))
  | 13%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 13%nat,30%nat => (rat.ratz (ssrint.Negz 0))
  | 14%nat,14%nat => (rat.ratz (ssrint.Posz 1))
  | 14%nat,29%nat => (rat.ratz (ssrint.Posz 1))
  | 15%nat,15%nat => (rat.ratz (ssrint.Posz 1))
  | 15%nat,28%nat => (rat.ratz (ssrint.Negz 0))
  | 16%nat,16%nat => (rat.ratz (ssrint.Posz 1))
  | 17%nat,17%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,18%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,19%nat => (rat.ratz (ssrint.Posz 1))
  | _,_ => rat.zeroq
  end.
Definition chart_upper_right := rational_data_matrix 20 32 chart_upper_right_data.
Definition chart_upper_decoder_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,1%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 0%nat,18%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 1%nat,0%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 1%nat,19%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 2%nat,3%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 2%nat,16%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 3%nat,2%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 3%nat,17%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 4%nat,5%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 4%nat,22%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 5%nat,4%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 5%nat,23%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 6%nat,7%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 6%nat,20%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 7%nat,6%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 7%nat,21%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 8%nat,9%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 8%nat,26%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 9%nat,8%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 9%nat,27%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 10%nat,11%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 10%nat,24%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 11%nat,10%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 11%nat,25%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 12%nat,13%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 12%nat,30%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 13%nat,12%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 13%nat,31%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 14%nat,15%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 14%nat,28%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 15%nat,14%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 15%nat,29%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 16%nat,2%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 16%nat,17%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 17%nat,3%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | 17%nat,16%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 18%nat,0%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 18%nat,19%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 19%nat,1%nat => (rat.divq (rat.ratz (ssrint.Negz 0)) (rat.ratz (ssrint.Posz 2)))
  | 19%nat,18%nat => (rat.divq (rat.ratz (ssrint.Posz 1)) (rat.ratz (ssrint.Posz 2)))
  | _,_ => rat.zeroq
  end.
Definition chart_upper_decoder := rational_data_matrix 20 32 chart_upper_decoder_data.
Definition chart_selector_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,0%nat => (rat.ratz (ssrint.Posz 1))
  | 1%nat,1%nat => (rat.ratz (ssrint.Posz 1))
  | 2%nat,2%nat => (rat.ratz (ssrint.Posz 1))
  | 3%nat,3%nat => (rat.ratz (ssrint.Posz 1))
  | 4%nat,4%nat => (rat.ratz (ssrint.Posz 1))
  | 5%nat,5%nat => (rat.ratz (ssrint.Posz 1))
  | 6%nat,6%nat => (rat.ratz (ssrint.Posz 1))
  | 7%nat,7%nat => (rat.ratz (ssrint.Posz 1))
  | 8%nat,8%nat => (rat.ratz (ssrint.Posz 1))
  | 9%nat,9%nat => (rat.ratz (ssrint.Posz 1))
  | 10%nat,10%nat => (rat.ratz (ssrint.Posz 1))
  | 11%nat,11%nat => (rat.ratz (ssrint.Posz 1))
  | 12%nat,12%nat => (rat.ratz (ssrint.Posz 1))
  | 13%nat,13%nat => (rat.ratz (ssrint.Posz 1))
  | 14%nat,14%nat => (rat.ratz (ssrint.Posz 1))
  | 15%nat,15%nat => (rat.ratz (ssrint.Posz 1))
  | 16%nat,16%nat => (rat.ratz (ssrint.Posz 1))
  | 17%nat,17%nat => (rat.ratz (ssrint.Posz 1))
  | 18%nat,18%nat => (rat.ratz (ssrint.Posz 1))
  | 19%nat,19%nat => (rat.ratz (ssrint.Posz 1))
  | _,_ => rat.zeroq
  end.
Definition chart_selector := rational_data_matrix 32 20 chart_selector_data.
Definition chart_pivot_left_data (row column : nat) : rat.rat :=
  match row,column with
  | 0%nat,0%nat => (rat.ratz (ssrint.Posz 2))
  | 1%nat,1%nat => (rat.ratz (ssrint.Posz 2))
  | 2%nat,2%nat => (rat.ratz (ssrint.Posz 2))
  | 3%nat,3%nat => (rat.ratz (ssrint.Posz 2))
  | 4%nat,4%nat => (rat.ratz (ssrint.Posz 2))
  | 4%nat,23%nat => (rat.ratz (ssrint.Posz 2))
  | 5%nat,5%nat => (rat.ratz (ssrint.Posz 2))
  | 5%nat,22%nat => (rat.ratz (ssrint.Negz 1))
  | 6%nat,6%nat => (rat.ratz (ssrint.Posz 2))
  | 6%nat,21%nat => (rat.ratz (ssrint.Posz 2))
  | 7%nat,7%nat => (rat.ratz (ssrint.Posz 2))
  | 7%nat,20%nat => (rat.ratz (ssrint.Negz 1))
  | 8%nat,8%nat => (rat.ratz (ssrint.Posz 2))
  | 8%nat,27%nat => (rat.ratz (ssrint.Posz 2))
  | 9%nat,9%nat => (rat.ratz (ssrint.Posz 2))
  | 9%nat,26%nat => (rat.ratz (ssrint.Negz 1))
  | 10%nat,10%nat => (rat.ratz (ssrint.Posz 2))
  | 10%nat,25%nat => (rat.ratz (ssrint.Posz 2))
  | 11%nat,11%nat => (rat.ratz (ssrint.Posz 2))
  | 11%nat,24%nat => (rat.ratz (ssrint.Negz 1))
  | 12%nat,12%nat => (rat.ratz (ssrint.Posz 2))
  | 12%nat,31%nat => (rat.ratz (ssrint.Posz 2))
  | 13%nat,13%nat => (rat.ratz (ssrint.Posz 2))
  | 13%nat,30%nat => (rat.ratz (ssrint.Negz 1))
  | 14%nat,14%nat => (rat.ratz (ssrint.Posz 2))
  | 14%nat,29%nat => (rat.ratz (ssrint.Posz 2))
  | 15%nat,15%nat => (rat.ratz (ssrint.Posz 2))
  | 15%nat,28%nat => (rat.ratz (ssrint.Negz 1))
  | 16%nat,16%nat => (rat.ratz (ssrint.Posz 2))
  | 17%nat,17%nat => (rat.ratz (ssrint.Posz 2))
  | 18%nat,18%nat => (rat.ratz (ssrint.Posz 2))
  | 19%nat,19%nat => (rat.ratz (ssrint.Posz 2))
  | _,_ => rat.zeroq
  end.
Definition chart_pivot_left := rational_data_matrix 20 32 chart_pivot_left_data.
Lemma chart_upper_factorization_data_checked : rational_data_equation_check 32 32
  (rational_sparse_data_product 20 chart_complement_data chart_upper_right_data) chart_center_data = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_upper_factorization : matrix.mulmx chart_complement chart_upper_right = chart_center.
Proof.
  pose proof (@rational_sparse_product_sound 32 20 32
    chart_complement_data chart_upper_right_data chart_center_data chart_upper_factorization_data_checked) as checked.
  exact checked.
Qed.
Lemma chart_decode_upper_center_data_checked : rational_data_equation_check 20 32
  (rational_sparse_data_product 32 chart_upper_decoder_data chart_center_data) chart_upper_right_data = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_decode_upper_center : matrix.mulmx chart_upper_decoder chart_center = chart_upper_right.
Proof.
  pose proof (@rational_sparse_product_sound 20 32 32
    chart_upper_decoder_data chart_center_data chart_upper_right_data chart_decode_upper_center_data_checked) as checked.
  exact checked.
Qed.
Lemma chart_select_upper_identity_data_checked : rational_data_equation_check 20 20
  (rational_sparse_data_product 32 chart_upper_right_data chart_selector_data) rational_data_identity = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_select_upper_identity : matrix.mulmx chart_upper_right chart_selector = (1%:M : matrix.matrix rat.rat 20 20).
Proof.
  pose proof (@rational_sparse_product_sound 20 32 20
    chart_upper_right_data chart_selector_data rational_data_identity chart_select_upper_identity_data_checked) as checked.
  rw (@rational_data_identity_matrix 20) in checked.
  exact checked.
Qed.
Lemma chart_kernel_residual_data_checked : rational_data_equation_check 32 12
  (rational_sparse_data_product 32 chart_center_data chart_kernel_data) rational_data_zero = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_kernel_residual : matrix.mulmx chart_center chart_kernel = (0 : matrix.matrix rat.rat 32 12).
Proof.
  pose proof (@rational_sparse_product_sound 32 32 12
    chart_center_data chart_kernel_data rational_data_zero chart_kernel_residual_data_checked) as checked.
  rw (@rational_data_zero_matrix 32 12) in checked.
  exact checked.
Qed.
Lemma chart_kernel_decode_data_checked : rational_data_equation_check 12 12
  (rational_sparse_data_product 32 chart_decoder_data chart_kernel_data) rational_data_identity = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_kernel_decode : matrix.mulmx chart_decoder chart_kernel = (1%:M : matrix.matrix rat.rat 12 12).
Proof.
  pose proof (@rational_sparse_product_sound 12 32 12
    chart_decoder_data chart_kernel_data rational_data_identity chart_kernel_decode_data_checked) as checked.
  rw (@rational_data_identity_matrix 12) in checked.
  exact checked.
Qed.
Lemma chart_complement_decode_zero_data_checked : rational_data_equation_check 12 20
  (rational_sparse_data_product 32 chart_decoder_data chart_complement_data) rational_data_zero = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_complement_decode_zero : matrix.mulmx chart_decoder chart_complement = (0 : matrix.matrix rat.rat 12 20).
Proof.
  pose proof (@rational_sparse_product_sound 12 32 20
    chart_decoder_data chart_complement_data rational_data_zero chart_complement_decode_zero_data_checked) as checked.
  rw (@rational_data_zero_matrix 12 20) in checked.
  exact checked.
Qed.
Lemma chart_basis_inverse_left_data_checked : rational_data_equation_check 32 32
  (rational_sparse_data_product 32 chart_basis_inverse_data chart_basis_data) rational_data_identity = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_basis_inverse_left : matrix.mulmx chart_basis_inverse chart_basis = (1%:M : matrix.matrix rat.rat 32 32).
Proof.
  pose proof (@rational_sparse_product_sound 32 32 32
    chart_basis_inverse_data chart_basis_data rational_data_identity chart_basis_inverse_left_data_checked) as checked.
  rw (@rational_data_identity_matrix 32) in checked.
  exact checked.
Qed.
Lemma chart_basis_inverse_right_data_checked : rational_data_equation_check 32 32
  (rational_sparse_data_product 32 chart_basis_data chart_basis_inverse_data) rational_data_identity = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_basis_inverse_right : matrix.mulmx chart_basis chart_basis_inverse = (1%:M : matrix.matrix rat.rat 32 32).
Proof.
  pose proof (@rational_sparse_product_sound 32 32 32
    chart_basis_data chart_basis_inverse_data rational_data_identity chart_basis_inverse_right_data_checked) as checked.
  rw (@rational_data_identity_matrix 32) in checked.
  exact checked.
Qed.
Lemma chart_pivot_left_identity_data_checked : rational_data_equation_check 20 32
  (rational_sparse_data_product 32 (fun row column => chart_complement_data column row) chart_center_data) chart_pivot_left_data = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_pivot_left_identity : matrix.mulmx (matrix.trmx chart_complement) chart_center = chart_pivot_left.
Proof.
  pose proof (@rational_sparse_product_sound 20 32 32
    (fun row column => chart_complement_data column row) chart_center_data chart_pivot_left_data chart_pivot_left_identity_data_checked) as checked.
  rw (@rational_data_transpose_matrix 32 20 chart_complement_data) in checked.
  exact checked.
Qed.
Lemma chart_pivot_right_identity_data_checked : rational_data_equation_check 20 20
  (rational_sparse_data_product 32 chart_pivot_left_data chart_complement_data) chart_pivot_data = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_pivot_right_identity : matrix.mulmx chart_pivot_left chart_complement = chart_pivot.
Proof.
  pose proof (@rational_sparse_product_sound 20 32 20
    chart_pivot_left_data chart_complement_data chart_pivot_data chart_pivot_right_identity_data_checked) as checked.
  exact checked.
Qed.
Lemma chart_pivot_inverse_left_data_checked : rational_data_equation_check 20 20
  (rational_sparse_data_product 20 chart_pivot_inverse_data chart_pivot_data) rational_data_identity = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_pivot_inverse_left : matrix.mulmx chart_pivot_inverse chart_pivot = (1%:M : matrix.matrix rat.rat 20 20).
Proof.
  pose proof (@rational_sparse_product_sound 20 20 20
    chart_pivot_inverse_data chart_pivot_data rational_data_identity chart_pivot_inverse_left_data_checked) as checked.
  rw (@rational_data_identity_matrix 20) in checked.
  exact checked.
Qed.
Lemma chart_pivot_inverse_right_data_checked : rational_data_equation_check 20 20
  (rational_sparse_data_product 20 chart_pivot_data chart_pivot_inverse_data) rational_data_identity = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_pivot_inverse_right : matrix.mulmx chart_pivot chart_pivot_inverse = (1%:M : matrix.matrix rat.rat 20 20).
Proof.
  pose proof (@rational_sparse_product_sound 20 20 20
    chart_pivot_data chart_pivot_inverse_data rational_data_identity chart_pivot_inverse_right_data_checked) as checked.
  rw (@rational_data_identity_matrix 20) in checked.
  exact checked.
Qed.

Definition chart_center_coefficients (index : SchreierSignCode.cube 5) : rat.rat :=
  if orb (Nat.eqb (cube_encode 5 index) 1) (Nat.eqb (cube_encode 5 index) 18)
  then 1 else 0.
Definition chart_actual_center_data row column :=
  @sparse_field_entry rat.rat_rat__canonical__GRing_Field 5 chart_center_coefficients
    (cube_decode 5 row) (cube_decode 5 column).
Lemma chart_actual_center_checked : rational_data_equation_check 32 32
  chart_actual_center_data chart_center_data = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chart_actual_center_matrix :
  @sparse_field_matrix rat.rat_rat__canonical__GRing_Field 5 chart_center_coefficients = chart_center.
Proof.
  change (rational_data_matrix 32 32 chart_actual_center_data = chart_center).
  exact (@rational_data_equation_sound 32 32 chart_actual_center_data chart_center_data chart_actual_center_checked).
Qed.
Theorem chart_center_exact_rank : @mxrank rat.rat_rat__canonical__GRing_Field 32 32 chart_center = 20%nat.
Proof.
  apply (@matrix_rank_witness_sound rat.rat_rat__canonical__GRing_Field 32 32 20
    chart_center chart_complement chart_upper_right chart_upper_decoder chart_selector).
  - symmetry; exact chart_upper_factorization.
  - rw chart_decode_upper_center. exact chart_select_upper_identity.
Qed.
Theorem chart_kernel_exact_rank : @mxrank rat.rat_rat__canonical__GRing_Field 32 12 chart_kernel = 12%nat.
Proof.
  apply (@matrix_rank_witness_sound rat.rat_rat__canonical__GRing_Field 32 12 12
    chart_kernel chart_kernel 1%:M chart_decoder 1%:M).
  - rw mulmx1. reflexivity.
  - rw chart_kernel_decode mulmx1. reflexivity.
Qed.
Theorem chart_kernel_coordinates
  (upper : matrix.matrix rat.rat 20 1) (lower : matrix.matrix rat.rat 12 1) :
  chart_decoder *m (chart_complement *m upper + chart_kernel *m lower) = lower.
Proof.
  rw mulmxDr !mulmxA chart_complement_decode_zero chart_kernel_decode mul0mx mul1mx add0r.
  reflexivity.
Qed.
Theorem chart_pivot_operator_identity :
  (matrix.trmx chart_complement) *m chart_center *m chart_complement = chart_pivot.
Proof. rw chart_pivot_left_identity. exact chart_pivot_right_identity. Qed.
Theorem chart_rational_kernel_complete : forall vector : matrix.matrix rat.rat 32 1,
  chart_center *m vector = 0 -> exists coefficients : matrix.matrix rat.rat 12 1,
  vector = chart_kernel *m coefficients.
Proof.
  apply (@full_dimension_column_kernel rat.rat_rat__canonical__GRing_Field 32 32 12 chart_center chart_kernel).
  - exact chart_kernel_residual.
  - rw chart_center_exact_rank chart_kernel_exact_rank. reflexivity.
Qed.
Theorem chart_real_kernel_complete : forall vector : matrix.matrix R 32 1,
  matrix.map_mx real_rational chart_center *m vector = 0 ->
  exists coefficients : matrix.matrix R 12 1,
    vector = matrix.map_mx real_rational chart_kernel *m coefficients.
Proof.
  apply (@rational_frame_real_complete 32 32 12 chart_center chart_kernel).
  - exact chart_kernel_residual.
  - rw chart_center_exact_rank chart_kernel_exact_rank. reflexivity.
Qed.
Theorem chart_recursive_center_rank :
  @mxrank StdlibRealFieldAdapter.stdlib_real_field (tower_dimension 5) (tower_dimension 5)
    (tower_left_matrix 5 (tower_from_coordinates 5
      (fun index => real_rational (chart_center_coefficients index)))) = 20%nat.
Proof.
  rw rational_sparse_tower_rank chart_actual_center_matrix. exact chart_center_exact_rank.
Qed.
Print Assumptions chart_actual_center_matrix.
Print Assumptions chart_center_exact_rank.
Print Assumptions chart_kernel_coordinates.
Print Assumptions chart_real_kernel_complete.
Print Assumptions chart_recursive_center_rank.
