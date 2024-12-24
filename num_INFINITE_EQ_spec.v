Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4628778 : forall s : nat -> Prop, (@INFINITE nat s) = (forall N : nat, exists n : nat, (Peano.le N n) /\ (@IN nat n s)).
