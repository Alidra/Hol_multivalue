Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem12860 : forall {A : Type'}, forall b : Prop, forall t : A, (@COND A b t t) = t.