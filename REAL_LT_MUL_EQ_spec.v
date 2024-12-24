Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1610545 : (forall x : real, forall y : real, (real_lt (real_of_num (NUMERAL 0)) x) -> (real_lt (real_of_num (NUMERAL 0)) (real_mul x y)) = (real_lt (real_of_num (NUMERAL 0)) y)) /\ (forall x : real, forall y : real, (real_lt (real_of_num (NUMERAL 0)) y) -> (real_lt (real_of_num (NUMERAL 0)) (real_mul x y)) = (real_lt (real_of_num (NUMERAL 0)) x)).
