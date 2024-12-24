Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term2 := (forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
