Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem17160 : forall (p : Prop) (q : Prop), (~ (p \/ q)) = ((~ p) /\ (~ q)).