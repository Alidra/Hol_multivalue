Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066089 : forall {A : Type'}, (forall a : A, forall f : nat -> A, (@FCONS A a f (NUMERAL 0)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (@FCONS A a f (S n)) = (f n)).
