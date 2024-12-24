Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem309993 : forall {A : Type'} (a : A) (f : A -> A), exists s : nat -> A, ((s (NUMERAL 0)) = a) /\ (forall n : nat, (s (S n)) = (f (s n))).
