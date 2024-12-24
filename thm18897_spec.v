Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18897 : forall {A : Type'} (P : A -> Prop), (@ex1 A P) = ((exists x : A, P x) /\ (forall x : A, forall y : A, (~ (P x)) \/ ((~ (P y)) \/ (y = x)))).
