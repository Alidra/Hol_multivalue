Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1491648 : forall x : real, forall y : real, (real_neg (real_mul x y)) = (real_mul x (real_neg y)).