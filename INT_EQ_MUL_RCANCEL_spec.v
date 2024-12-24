Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301754 : forall x : int, forall y : int, forall z : int, ((int_mul x z) = (int_mul y z)) = ((x = y) \/ (z = (int_of_num (NUMERAL 0)))).
