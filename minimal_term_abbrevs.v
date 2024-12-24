Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => @ε nat (fun y1 : nat => (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))) x0.
Definition term2 (x0 : nat -> Prop) := @ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term3 := forall y0 : nat -> Prop, (minimal y0) = (@ε nat (fun y1 : nat => (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2)))).
Definition term0 := fun y0 : nat -> Prop => @ε nat (fun y1 : nat => (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))).
Definition term4 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (minimal y0) = (@ε nat (fun y1 : nat => (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))))) x0.
