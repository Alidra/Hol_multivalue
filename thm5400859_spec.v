Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400859 : forall (m : nat) (n : nat), (((Peano.le m (S n)) -> (dotdot m (S n)) = (@INSERT nat (S n) (dotdot m n))) /\ ((~ (Peano.le m (S n))) -> (dotdot m (S n)) = (dotdot m n))) = ((dotdot m (S n)) = (@COND (nat -> Prop) (Peano.le m (S n)) (@INSERT nat (S n) (dotdot m n)) (dotdot m n))).
