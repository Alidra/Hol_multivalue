Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) x0.
Definition term1 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term2 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
