Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem90226 : forall n : nat, forall m : nat, (Peano.ge m n) = (Peano.le n m).
