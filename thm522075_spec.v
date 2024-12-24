Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522075 : (forall n : nat, (Peano.le n 0) = ((Peano.le n 0) /\ (Peano.le 0 n))) /\ ((forall n : nat, (Peano.le n 0) = ((Peano.le 0 n) /\ (Peano.le n 0))) /\ ((forall m : nat, forall n : nat, ~ ((Peano.le m n) /\ (Peano.lt n m))) /\ (forall m : nat, forall n : nat, ~ ((Peano.lt m n) /\ (Peano.le n m))))).
