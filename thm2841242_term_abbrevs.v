Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) (NUMERAL x0).
Definition term1 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num (NUMERAL x0)) (int_of_num y0)) = (int_of_num (Nat.mul (NUMERAL x0) y0)).
