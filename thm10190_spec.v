Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem10190 : (forall t : Prop, (~ (~ t)) = t) = (forall t : Prop, (~ (~ t)) = t).
