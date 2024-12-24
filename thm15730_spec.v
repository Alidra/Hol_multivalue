Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem15730 : forall (r : Prop), r = ((one_REP (one_ABS r)) = r).
