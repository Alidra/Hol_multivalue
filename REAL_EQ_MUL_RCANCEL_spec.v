Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1587429 : forall x : real, forall y : real, forall z : real, ((real_mul x z) = (real_mul y z)) = ((x = y) \/ (z = (real_of_num (NUMERAL 0)))).
