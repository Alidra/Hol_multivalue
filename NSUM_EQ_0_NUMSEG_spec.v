Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7044635 : forall f : nat -> nat, forall m : nat, forall n : nat, (forall i : nat, ((Peano.le m i) /\ (Peano.le i n)) -> (f i) = (NUMERAL 0)) -> (@nsum nat (dotdot m n) f) = (NUMERAL 0).
