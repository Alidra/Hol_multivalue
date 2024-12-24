Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21568 : forall (b : Prop), (True = b) -> b \/ (~ True).
