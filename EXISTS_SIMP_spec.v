Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1121 : forall {A : Type'}, forall t : Prop, (exists x : A, t) = t.
