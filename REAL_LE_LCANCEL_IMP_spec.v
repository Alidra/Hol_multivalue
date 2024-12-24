Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1599019 : forall x : real, forall y : real, forall z : real, ((real_lt (real_of_num (NUMERAL 0)) x) /\ (real_le (real_mul x y) (real_mul x z))) -> real_le y z.
