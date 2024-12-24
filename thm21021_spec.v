Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21021 : forall (p : Prop), True = ((~ p) = (p -> False)).
