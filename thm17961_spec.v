Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem17961 : forall {A : Type'} (P : A -> Prop), ((fun P' : A -> Prop => (~ (forall x : A, P' x)) = (exists x : A, ~ (P' x))) P) = ((~ (forall x : A, P x)) = (exists x : A, ~ (P x))).
