Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21028 : forall (p : Prop), ((p -> ~ p) = (~ p)) = ((p -> ~ p) = (~ p)).