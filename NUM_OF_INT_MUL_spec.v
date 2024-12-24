Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2835697 : forall x : int, forall y : int, ((int_le (int_of_num (NUMERAL 0)) x) /\ (int_le (int_of_num (NUMERAL 0)) y)) -> (num_of_int (int_mul x y)) = (Nat.mul (num_of_int x) (num_of_int y)).
