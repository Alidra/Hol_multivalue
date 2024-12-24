Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982773 : forall (x : real) (y : real) (q : nat), (real_pow (real_mul x y) q) = (real_mul (real_pow x q) (real_pow y q)).
