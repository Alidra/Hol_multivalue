Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21460 : forall (b : Prop), (True -> b) = ((~ True) \/ b).
