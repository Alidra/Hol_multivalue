Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4624119 : forall s : nat -> Prop, (@FINITE nat s) = (exists a : nat, forall x : nat, (@IN nat x s) -> Peano.le x a).
