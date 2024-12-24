Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem22403 : forall a : Prop, forall b : Prop, ((~ a) -> b) = (a \/ b).
