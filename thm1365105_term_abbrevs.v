Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := ((True /\ False) = False) /\ ((True /\ True) = True).
Definition term1 := ((False /\ True) = False) /\ (((True /\ False) = False) /\ ((True /\ True) = True)).
