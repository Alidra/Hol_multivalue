Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1487144 : forall x : real, forall y : real, forall z : real, (real_mul (real_add x y) z) = (real_add (real_mul x z) (real_mul y z)).
