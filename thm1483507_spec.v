Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483507 : forall (x : real) (q : nat), (real_pow x (S q)) = (real_mul x (real_pow x q)).
