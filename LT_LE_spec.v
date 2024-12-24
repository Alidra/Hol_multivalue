Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem97539 : forall m : nat, forall n : nat, (Peano.lt m n) = ((Peano.le m n) /\ (~ (m = n))).
