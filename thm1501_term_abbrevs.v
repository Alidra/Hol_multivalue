Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := ((~ False) -> True) /\ (True -> ~ False).
Definition term1 := True -> ~ False.
Definition term0 := (~ False) -> True.
