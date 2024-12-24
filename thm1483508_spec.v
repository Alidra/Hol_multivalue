Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483508 : forall (y : real) (x : real) (z : real), (real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z)).
