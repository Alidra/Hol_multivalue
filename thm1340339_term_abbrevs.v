Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : nat) := forall y0 : nat, treal_eq (treal_add (treal_of_num x0) (treal_of_num y0)) (treal_of_num (Nat.add x0 y0)).
Definition term4 (x0 : nat) (x1 : nat) := treal_add (treal_of_num x0) (treal_of_num x1).
Definition term14 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num x0) (real_of_num x1)).
Definition term17 (x0 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term12 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term8 (x0 : nat) (x1 : nat) := real_add (mk_real (treal_eq (treal_of_num x0))) (mk_real (treal_eq (treal_of_num x1))).
Definition term23 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term22 := forall y0 : nat, forall y1 : nat, treal_eq (treal_add (treal_of_num y0) (treal_of_num y1)) (treal_of_num (Nat.add y0 y1)).
Definition term1 (x0 : nat) (x1 : nat) := treal_eq (treal_add (treal_of_num x0) (treal_of_num x1)) (treal_of_num (Nat.add x0 x1)).
Definition term2 (x0 : nat) (x1 : nat) := mk_real (treal_eq (treal_add (treal_of_num x0) (treal_of_num x1))).
Definition term9 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term16 (x0 : nat) := fun y0 : nat => treal_eq (treal_add (treal_of_num x0) (treal_of_num y0)) (treal_of_num (Nat.add x0 y0)).
Definition term0 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term11 (x0 : nat) := real_add (real_of_num x0).
Definition term19 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term13 (x0 : nat) (x1 : nat) := @eq real (mk_real (treal_eq (treal_add (treal_of_num x0) (treal_of_num x1)))).
Definition term10 (x0 : nat) := real_add (mk_real (treal_eq (treal_of_num x0))).
Definition term3 (x0 : nat) (x1 : nat) := mk_real (treal_eq (treal_of_num (Nat.add x0 x1))).
Definition term5 (x0 : nat) (x1 : nat) := treal_of_num (Nat.add x0 x1).
Definition term21 := fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term20 := fun y0 : nat => forall y1 : nat, treal_eq (treal_add (treal_of_num y0) (treal_of_num y1)) (treal_of_num (Nat.add y0 y1)).
Definition term7 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_add (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term6 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (treal_add x0 x1)).
Definition term15 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
