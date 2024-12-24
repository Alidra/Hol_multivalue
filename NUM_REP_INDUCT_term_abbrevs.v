Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : ind -> Prop, ((y0 IND_0) /\ (forall y1 : ind, (y0 y1) -> y0 (IND_SUC y1))) -> forall y1 : ind, (NUM_REP y1) -> y0 y1.
