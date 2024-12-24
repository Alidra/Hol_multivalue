Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5413112 : forall (m : nat) (n : nat), (Peano.le m (S n)) -> forall x : nat, ((Peano.le m x) /\ (Peano.le x (S n))) = ((x = (S n)) \/ ((Peano.le m x) /\ (Peano.le x n))).
