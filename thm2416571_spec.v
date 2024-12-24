Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416571 : forall (x : int) (q : nat), (int_mul (int_pow x q) x) = (int_pow x (S q)).
