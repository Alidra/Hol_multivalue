Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516656 : forall (n : nat), (~ ((S n) = 0)) -> ((S n) = 0) = False.
