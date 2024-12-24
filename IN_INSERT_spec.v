Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3205665 : forall {A : Type'}, forall x : A, forall y : A, forall s : A -> Prop, (@IN A x (@INSERT A y s)) = ((x = y) \/ (@IN A x s)).
