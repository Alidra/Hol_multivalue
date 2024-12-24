Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5401059 : forall (m : nat) (n : nat), (forall x : nat, ((Peano.le m x) /\ (Peano.le x (S n))) = ((Peano.le m x) /\ (Peano.le x n))) = (forall x : nat, (@IN nat x (dotdot m (S n))) = (@IN nat x (dotdot m n))).
