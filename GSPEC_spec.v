Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3182122 : forall {A : Type'}, forall p : A -> Prop, (@GSPEC A p) = p.
