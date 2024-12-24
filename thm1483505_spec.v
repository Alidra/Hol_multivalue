Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483505 : forall (y : real) (z : real) (x : real) (q : nat), ((real_mul x (real_add y z)) = (real_add (real_mul x y) (real_mul x z))) /\ ((real_pow x (S q)) = (real_mul x (real_pow x q))).
