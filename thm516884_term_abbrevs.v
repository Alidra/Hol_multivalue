Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := @eq Prop (Peano.le x0 (NUMERAL 0)).
Definition term8 := and (forall y0 : nat, (Peano.le y0 0) = (y0 = 0)).
Definition term7 := and (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))).
Definition term6 := forall y0 : nat, (Peano.le y0 0) = (y0 = 0).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term2 (x0 : nat) := @eq Prop (Peano.le x0 0).
Definition term3 := fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term11 := (forall y0 : nat, (Peano.le y0 0) = (y0 = 0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term10 := (forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))).
Definition term4 := fun y0 : nat => (Peano.le y0 0) = (y0 = 0).
Definition term5 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term0 (x0 : nat) := Peano.le x0 (NUMERAL 0).
