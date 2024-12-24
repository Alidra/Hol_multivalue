Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat -> Prop) := (x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0)).
Definition term1 (x0 : nat -> Prop) := and (x0 0).
Definition term10 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term2 (x0 : nat -> Prop) := and (x0 (NUMERAL 0)).
Definition term6 (x0 : nat -> Prop) := imp ((x0 0) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))).
Definition term9 (x0 : nat -> Prop) := ((x0 0) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term7 (x0 : nat -> Prop) := imp ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))).
Definition term4 (x0 : nat -> Prop) := (x0 0) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0)).
Definition term12 := fun y0 : nat -> Prop => ((y0 (NUMERAL 0)) /\ (forall y1 : nat, (y0 y1) -> y0 (S y1))) -> forall y1 : nat, y0 y1.
Definition term11 := fun y0 : nat -> Prop => ((y0 0) /\ (forall y1 : nat, (y0 y1) -> y0 (S y1))) -> forall y1 : nat, y0 y1.
Definition term14 := forall y0 : nat -> Prop, ((y0 (NUMERAL 0)) /\ (forall y1 : nat, (y0 y1) -> y0 (S y1))) -> forall y1 : nat, y0 y1.
Definition term13 := forall y0 : nat -> Prop, ((y0 0) /\ (forall y1 : nat, (y0 y1) -> y0 (S y1))) -> forall y1 : nat, y0 y1.
Definition term0 (x0 : nat -> Prop) := x0 (NUMERAL 0).
Definition term3 (x0 : nat -> Prop) := forall y0 : nat, (x0 y0) -> x0 (S y0).
Definition term8 (x0 : nat -> Prop) := forall y0 : nat, x0 y0.
