Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16506 : forall (t : Prop), (fun t' : Prop => (~ (~ t')) = t') t.
