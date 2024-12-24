Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (NUM_REP IND_0) /\ (forall y0 : ind, (NUM_REP y0) -> NUM_REP (IND_SUC y0)).
