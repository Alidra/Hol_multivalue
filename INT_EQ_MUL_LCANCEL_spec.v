Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301711 : forall x : int, forall y : int, forall z : int, ((int_mul x y) = (int_mul x z)) = ((x = (int_of_num (NUMERAL 0))) \/ (y = z)).
