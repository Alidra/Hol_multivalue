Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7047279 : forall (f : nat -> nat), (forall m : nat, (@nsum nat (dotdot m (NUMERAL 0)) f) = (@COND nat (m = (NUMERAL 0)) (f (NUMERAL 0)) (NUMERAL 0))) /\ (forall m : nat, forall n : nat, (@nsum nat (dotdot m (S n)) f) = (@COND nat (Peano.le m (S n)) (Nat.add (@nsum nat (dotdot m n) f) (f (S n))) (@nsum nat (dotdot m n) f))).
