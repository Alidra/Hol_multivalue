Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := and ((Nat.pred (NUMERAL 0)) = (NUMERAL 0)).
Definition term5 := forall y0 : nat, (Nat.pred (S y0)) = y0.
Definition term4 := and ((Nat.pred 0) = 0).
Definition term6 := ((Nat.pred (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, (Nat.pred (S y0)) = y0).
Definition term2 := @eq nat (Nat.pred 0).
Definition term0 := Nat.pred (NUMERAL 0).
Definition term7 := ((Nat.pred 0) = 0) /\ (forall y0 : nat, (Nat.pred (S y0)) = y0).
Definition term1 := @eq nat (Nat.pred (NUMERAL 0)).
