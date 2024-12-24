Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := real_abs (real_of_num x0).
Definition term6 (x0 : nat) := real_of_int (int_abs (int_of_num x0)).
Definition term8 (x0 : nat) := @eq real (real_of_int (int_abs (int_of_num x0))).
Definition term10 := forall y0 : nat, (int_abs (int_of_num y0)) = (int_of_num y0).
Definition term5 (x0 : int) := real_of_int (int_abs x0).
Definition term2 (x0 : nat) := real_of_int (int_of_num x0).
Definition term3 (x0 : nat) := real_abs (real_of_int (int_of_num x0)).
Definition term0 (x0 : nat) := (fun y0 : nat => (real_abs (real_of_num y0)) = (real_of_num y0)) x0.
Definition term9 (x0 : nat) := int_abs (int_of_num x0).
Definition term4 (x0 : int) := real_abs (real_of_int x0).
Definition term7 (x0 : nat) := @eq real (real_abs (real_of_num x0)).
