Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.mul (NUMERAL x0) y0)) = (int_mul (int_of_num (NUMERAL x0)) (int_of_num y0))) x1.
