Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400908 : forall (m : nat) (n : nat), (forall x : nat, (@IN nat x (dotdot m (S n))) = (@IN nat x (@INSERT nat (S n) (dotdot m n)))) = ((dotdot m (S n)) = (@INSERT nat (S n) (dotdot m n))).
