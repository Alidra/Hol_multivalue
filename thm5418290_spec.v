Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5418290 : forall (m : nat) (h1 : m = (NUMERAL 0)), forall x : nat, (@IN nat x (dotdot m (NUMERAL 0))) = (@IN nat x (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
