Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5418304 : forall (m : nat) (n : nat), (dotdot m (S n)) = (@COND (nat -> Prop) (Peano.le m (S n)) (@INSERT nat (S n) (dotdot m n)) (dotdot m n)).
