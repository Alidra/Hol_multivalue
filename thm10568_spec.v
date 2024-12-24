Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem10568 : forall (b : Prop) (a : Prop), (a -> b) = ((~ b) -> ~ a).
