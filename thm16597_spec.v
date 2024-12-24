Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16597 : forall (a : Prop) (b : Prop) (h1 : ~ (a \/ b)), ~ a.
