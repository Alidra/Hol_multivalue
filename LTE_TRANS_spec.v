Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem95941 : forall m : nat, forall n : nat, forall p : nat, ((Peano.lt m n) /\ (Peano.le n p)) -> Peano.lt m p.
