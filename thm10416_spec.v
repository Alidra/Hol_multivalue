Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem10416 : forall (t : Prop), (fun t' : Prop => (~ (~ t')) = t') t.
