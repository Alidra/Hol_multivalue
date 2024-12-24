Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2428623 : forall x : real, forall y : real, forall n : real, (real_mod n x y) = (exists q : real, (integer q) /\ ((real_sub x y) = (real_mul q n))).
