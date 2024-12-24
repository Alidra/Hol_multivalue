Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516884 : (forall m : nat, (Peano.le m 0) = (m = 0)) /\ (forall m : nat, forall n : nat, (Peano.le m (S n)) = ((m = (S n)) \/ (Peano.le m n))).
