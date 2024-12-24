Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301825 : forall x : int, forall y : int, forall z : int, ((~ (z = (int_of_num (NUMERAL 0)))) /\ ((int_mul x z) = (int_mul y z))) -> x = y.
