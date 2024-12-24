Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem365462 : forall {A : Type'}, forall m : A -> nat, @WF A (@MEASURE A m).
