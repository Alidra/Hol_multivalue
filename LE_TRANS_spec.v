Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem93743 : forall m : nat, forall n : nat, forall p : nat, ((Peano.le m n) /\ (Peano.le n p)) -> Peano.le m p.
