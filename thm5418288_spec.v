Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5418288 : forall (m : nat) (n : nat) (h1 : Peano.le m (S n)), forall x : nat, (@IN nat x (dotdot m (S n))) = (@IN nat x (@INSERT nat (S n) (dotdot m n))).
