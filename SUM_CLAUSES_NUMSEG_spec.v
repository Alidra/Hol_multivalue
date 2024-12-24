Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7221724 : forall (f : nat -> real), (forall m : nat, (@sum nat (dotdot m (NUMERAL 0)) f) = (@COND real (m = (NUMERAL 0)) (f (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ (forall m : nat, forall n : nat, (@sum nat (dotdot m (S n)) f) = (@COND real (Peano.le m (S n)) (real_add (@sum nat (dotdot m n) f) (f (S n))) (@sum nat (dotdot m n) f))).
