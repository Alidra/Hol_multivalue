Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21005 : forall (b : Prop) (a : Prop) (h1 : a = True), ((~ a) \/ (~ b)) = (~ (a /\ b)).
