Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1584766 : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (NUMERAL 0)) x) /\ (real_lt y z)) -> real_lt (real_mul x y) (real_mul x z).
