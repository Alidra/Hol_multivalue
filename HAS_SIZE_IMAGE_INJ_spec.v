Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4004559 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall n : nat, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@HAS_SIZE A s n)) -> @HAS_SIZE B (@IMAGE A B f s) n.
