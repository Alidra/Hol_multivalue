Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400957 : forall (m : nat), (forall x : nat, ((Peano.le m x) /\ (Peano.le x (NUMERAL 0))) = (x = (NUMERAL 0))) = (forall x : nat, (@IN nat x (dotdot m (NUMERAL 0))) = (@IN nat x (@INSERT nat (NUMERAL 0) (@EMPTY nat)))).
