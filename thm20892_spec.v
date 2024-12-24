Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem20892 : forall (b : Prop) (a : Prop) (h1 : a = False), (~ (a \/ b)) = ((~ a) /\ (~ b)).
