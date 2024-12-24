Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem75635 : forall {A : Type'}, forall e : A, forall f : A -> nat -> A, exists fn : nat -> A, ((fn (NUMERAL 0)) = e) /\ (forall n : nat, (fn (S n)) = (f (fn n) n)).
