Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7214061 : forall f : nat -> real, forall m : nat, forall n : nat, (forall i : nat, ((Peano.le m i) /\ (Peano.le i n)) -> (f i) = (real_of_num (NUMERAL 0))) -> (@sum nat (dotdot m n) f) = (real_of_num (NUMERAL 0)).
