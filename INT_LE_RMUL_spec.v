Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303202 : forall x : int, forall y : int, forall z : int, ((int_le x y) /\ (int_le (int_of_num (NUMERAL 0)) z)) -> int_le (int_mul x z) (int_mul y z).
