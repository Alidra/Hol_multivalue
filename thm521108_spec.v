Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem521108 : forall (n : nat), (Peano.le 0 n) = ((Peano.le 0 n) = True).