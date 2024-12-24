Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1583207 : forall x : real, forall y : real, forall z : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ (real_le y z)) -> real_le (real_mul x y) (real_mul x z).
