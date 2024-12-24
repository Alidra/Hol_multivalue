Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem98377 : forall m : nat, forall n : nat, (~ (Peano.lt m n)) = (Peano.le n m).
