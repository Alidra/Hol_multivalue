Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1584226 : forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_le (real_of_num (NUMERAL 0)) z)) -> real_le (real_mul x z) (real_mul y z).
