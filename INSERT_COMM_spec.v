Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3278336 : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@INSERT A x (@INSERT A y s)) = (@INSERT A y (@INSERT A x s)).
