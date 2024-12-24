Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5418330 : (forall m : nat, (dotdot m (NUMERAL 0)) = (@COND (nat -> Prop) (m = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat))) /\ (forall m : nat, forall n : nat, (dotdot m (S n)) = (@COND (nat -> Prop) (Peano.le m (S n)) (@INSERT nat (S n) (dotdot m n)) (dotdot m n))).
