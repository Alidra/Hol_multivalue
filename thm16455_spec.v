Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16455 : forall {A : Type'} (t : Prop), ((fun t' : Prop => (exists x : A, t') = t') t) = ((exists x : A, t) = t).
