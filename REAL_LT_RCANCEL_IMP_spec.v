Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1598629 : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (NUMERAL 0)) z) /\ (real_lt (real_mul x z) (real_mul y z))) -> real_lt x y.