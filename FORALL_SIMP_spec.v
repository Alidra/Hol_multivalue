Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1096 : forall {A : Type'}, forall t : Prop, (forall x : A, t) = t.