Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) (x1 : nat) := real_pow (real_of_int (int_of_num x0)) x1.
Definition term12 (x0 : nat) (x1 : nat) := real_of_int (int_pow (int_of_num x0) x1).
Definition term5 (x0 : nat) (x1 : nat) := real_of_num (Nat.pow x0 x1).
Definition term6 (x0 : nat) := real_of_int (int_of_num x0).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) x1.
Definition term17 (x0 : nat) (x1 : nat) := int_of_num (Nat.pow x0 x1).
Definition term0 := forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)).
Definition term18 (x0 : nat) := forall y0 : nat, (int_pow (int_of_num x0) y0) = (int_of_num (Nat.pow x0 y0)).
Definition term10 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))) x0.
Definition term16 (x0 : nat) (x1 : nat) := int_pow (int_of_num x0) x1.
Definition term13 (x0 : nat) (x1 : nat) := @eq real (real_pow (real_of_num x0) x1).
Definition term7 (x0 : nat) := real_pow (real_of_num x0).
Definition term2 (x0 : nat) := forall y0 : nat, (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term4 (x0 : nat) (x1 : nat) := real_pow (real_of_num x0) x1.
Definition term15 (x0 : nat) (x1 : nat) := real_of_int (int_of_num (Nat.pow x0 x1)).
Definition term11 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term8 (x0 : nat) := real_pow (real_of_int (int_of_num x0)).
Definition term14 (x0 : nat) (x1 : nat) := @eq real (real_of_int (int_pow (int_of_num x0) x1)).
