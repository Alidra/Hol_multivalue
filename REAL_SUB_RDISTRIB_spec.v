Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1526749 : forall x : real, forall y : real, forall z : real, (real_mul (real_sub x y) z) = (real_sub (real_mul x z) (real_mul y z)).
