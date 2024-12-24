Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1526444 : forall x : real, forall y : real, forall z : real, (real_mul x (real_sub y z)) = (real_sub (real_mul x y) (real_mul x z)).
