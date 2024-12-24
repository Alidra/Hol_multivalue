Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : nat) := forall y0 : nat, nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num y0)) (nadd_of_num (Nat.mul x0 y0)).
Definition term12 (x0 : nat) (x1 : nat) := hreal_mul (hreal_of_num x0) (hreal_of_num x1).
Definition term7 (x0 : nadd) (x1 : nadd) := hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term3 (x0 : nat) (x1 : nat) := mk_hreal (nadd_eq (nadd_of_num (Nat.mul x0 x1))).
Definition term13 (x0 : nat) (x1 : nat) := @eq hreal (mk_hreal (nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num x1)))).
Definition term19 (x0 : nat) := forall y0 : nat, (hreal_mul (hreal_of_num x0) (hreal_of_num y0)) = (hreal_of_num (Nat.mul x0 y0)).
Definition term5 (x0 : nat) (x1 : nat) := nadd_of_num (Nat.mul x0 x1).
Definition term17 (x0 : nat) := fun y0 : nat => (hreal_mul (hreal_of_num x0) (hreal_of_num y0)) = (hreal_of_num (Nat.mul x0 y0)).
Definition term10 (x0 : nat) := hreal_mul (mk_hreal (nadd_eq (nadd_of_num x0))).
Definition term8 (x0 : nat) (x1 : nat) := hreal_mul (mk_hreal (nadd_eq (nadd_of_num x0))) (mk_hreal (nadd_eq (nadd_of_num x1))).
Definition term2 (x0 : nat) (x1 : nat) := mk_hreal (nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num x1))).
Definition term9 (x0 : nat) := mk_hreal (nadd_eq (nadd_of_num x0)).
Definition term16 (x0 : nat) := fun y0 : nat => nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num y0)) (nadd_of_num (Nat.mul x0 y0)).
Definition term23 := forall y0 : nat, forall y1 : nat, (hreal_mul (hreal_of_num y0) (hreal_of_num y1)) = (hreal_of_num (Nat.mul y0 y1)).
Definition term22 := forall y0 : nat, forall y1 : nat, nadd_eq (nadd_mul (nadd_of_num y0) (nadd_of_num y1)) (nadd_of_num (Nat.mul y0 y1)).
Definition term0 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term1 (x0 : nat) (x1 : nat) := nadd_eq (nadd_mul (nadd_of_num x0) (nadd_of_num x1)) (nadd_of_num (Nat.mul x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := nadd_mul (nadd_of_num x0) (nadd_of_num x1).
Definition term14 (x0 : nat) (x1 : nat) := @eq hreal (hreal_mul (hreal_of_num x0) (hreal_of_num x1)).
Definition term11 (x0 : nat) := hreal_mul (hreal_of_num x0).
Definition term21 := fun y0 : nat => forall y1 : nat, (hreal_mul (hreal_of_num y0) (hreal_of_num y1)) = (hreal_of_num (Nat.mul y0 y1)).
Definition term20 := fun y0 : nat => forall y1 : nat, nadd_eq (nadd_mul (nadd_of_num y0) (nadd_of_num y1)) (nadd_of_num (Nat.mul y0 y1)).
Definition term15 (x0 : nat) (x1 : nat) := hreal_of_num (Nat.mul x0 x1).
Definition term6 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_mul x0 x1)).
