Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4784136 : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) = (exists f : nat -> A, (forall x : nat, @IN A (f x) s) /\ (forall x : nat, forall y : nat, ((f x) = (f y)) -> x = y)).
