Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16799 : forall (a : Prop) (b : Prop) (h1 : ~ a) (h2 : ~ b), ~ (a \/ b).
