Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem92426 : forall m : nat, forall n : nat, ((Peano.le m n) /\ (Peano.le n m)) = (m = n).
