Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term0 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => ((y0 (NUMERAL 0)) /\ (forall y1 : nat, (y0 y1) -> y0 (S y1))) -> forall y1 : nat, y0 y1) x0.