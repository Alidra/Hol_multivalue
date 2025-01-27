Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) (x1 : nat) (x2 : nat) := @eq real (real_of_int (int_pow x0 (Nat.add x1 x2))).
Definition term19 (x0 : nat) (x1 : int) (x2 : nat) := int_mul (int_pow x1 x0) (int_pow x1 x2).
Definition term15 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow (real_of_int x0) (Nat.add y0 y1)) = (real_mul (real_pow (real_of_int x0) y0) (real_pow (real_of_int x0) y1))) x1.
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.add y1 y2)) = (real_mul (real_pow y0 y1) (real_pow y0 y2))) (real_of_int x0).
Definition term4 (x0 : nat) (x1 : int) (x2 : nat) := (fun y0 : nat => (real_pow (real_of_int x1) (Nat.add x0 y0)) = (real_mul (real_pow (real_of_int x1) x0) (real_pow (real_of_int x1) y0))) x2.
Definition term13 (x0 : int) (x1 : nat) := real_mul (real_of_int (int_pow x0 x1)).
Definition term21 (x0 : int) := forall y0 : nat, forall y1 : nat, (int_pow x0 (Nat.add y0 y1)) = (int_mul (int_pow x0 y0) (int_pow x0 y1)).
Definition term1 (x0 : int) := forall y0 : nat, forall y1 : nat, (real_pow (real_of_int x0) (Nat.add y0 y1)) = (real_mul (real_pow (real_of_int x0) y0) (real_pow (real_of_int x0) y1)).
Definition term18 (x0 : int) (x1 : nat) (x2 : nat) := int_pow x0 (Nat.add x1 x2).
Definition term22 := forall y0 : int, forall y1 : nat, forall y2 : nat, (int_pow y0 (Nat.add y1 y2)) = (int_mul (int_pow y0 y1) (int_pow y0 y2)).
Definition term7 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term20 (x0 : nat) (x1 : int) := forall y0 : nat, (int_pow x1 (Nat.add x0 y0)) = (int_mul (int_pow x1 x0) (int_pow x1 y0)).
Definition term3 (x0 : nat) (x1 : int) := forall y0 : nat, (real_pow (real_of_int x1) (Nat.add x0 y0)) = (real_mul (real_pow (real_of_int x1) x0) (real_pow (real_of_int x1) y0)).
Definition term14 (x0 : nat) (x1 : int) (x2 : nat) := real_mul (real_of_int (int_pow x1 x0)) (real_of_int (int_pow x1 x2)).
Definition term9 (x0 : int) (x1 : nat) (x2 : nat) := real_of_int (int_pow x0 (Nat.add x1 x2)).
Definition term5 (x0 : int) (x1 : nat) (x2 : nat) := real_pow (real_of_int x0) (Nat.add x1 x2).
Definition term10 (x0 : int) (x1 : nat) (x2 : nat) := @eq real (real_pow (real_of_int x0) (Nat.add x1 x2)).
Definition term6 (x0 : nat) (x1 : int) (x2 : nat) := real_mul (real_pow (real_of_int x1) x0) (real_pow (real_of_int x1) x2).
Definition term16 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term8 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term17 (x0 : nat) (x1 : int) (x2 : nat) := real_of_int (int_mul (int_pow x1 x0) (int_pow x1 x2)).
Definition term12 (x0 : int) (x1 : nat) := real_mul (real_pow (real_of_int x0) x1).
