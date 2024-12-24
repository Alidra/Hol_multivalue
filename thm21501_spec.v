Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21501 : forall (b : Prop) (a : Prop), ((a = b) -> b \/ (~ a)) = ((a = b) -> b \/ (~ a)).
