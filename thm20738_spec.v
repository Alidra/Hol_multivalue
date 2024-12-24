Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20738 : forall (b : Prop), (True \/ b) = ((~ b) -> True).
