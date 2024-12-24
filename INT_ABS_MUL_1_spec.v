Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338225 : forall x : int, forall y : int, ((int_abs (int_mul x y)) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs x) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_abs y) = (int_of_num (NUMERAL (BIT1 0))))).
