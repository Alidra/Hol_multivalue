Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 := fun y0 : nat -> Prop => True.
Definition term2 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1.
Definition term7 := forall y0 : nat -> Prop, True.
Definition term5 := fun y0 : nat -> Prop => (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
Definition term9 (x0 : Prop) := forall y0 : nat -> Prop, x0.
Definition term0 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1) x0.
Definition term1 (x0 : nat -> Prop) := (forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) -> x0 y0) -> forall y0 : nat, x0 y0.
Definition term4 := forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
Definition term3 (x0 : type1605) := forall y0 : nat -> Prop, (forall y1 : nat, (forall y2 : nat, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : nat, y0 y1.
