Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, (Nat.pred (S y0)) = y0.
Definition term2 := ((Nat.pred (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (Nat.pred (S y0)) = y0).
Definition term1 := Nat.pred (NUMERAL 0).