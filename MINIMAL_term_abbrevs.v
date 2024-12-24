Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : nat) (x1 : nat -> Prop) := imp (Peano.lt x0 (@ε nat (fun y0 : nat => (x1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x1 y1))))).
Definition term17 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term3 := fun y0 : nat -> Prop => (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) = (exists y1 : nat, y0 y1).
Definition term2 := fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))).
Definition term11 (x0 : nat -> Prop) := and (x0 (minimal x0)).
Definition term21 (x0 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 (@ε nat (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))))) -> ~ (x0 y0).
Definition term13 (x0 : nat) (x1 : nat -> Prop) := Peano.lt x0 (minimal x1).
Definition term25 (x0 : nat -> Prop) := (x0 (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))))) /\ (forall y0 : nat, (Peano.lt y0 (@ε nat (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))))) -> ~ (x0 y0)).
Definition term6 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) = (exists y1 : nat, y0 y1)) x0.
Definition term12 (x0 : nat -> Prop) := and (x0 (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))))).
Definition term8 (x0 : nat -> Prop) := @ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))).
Definition term18 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (minimal x0)) -> ~ (x0 x1).
Definition term10 (x0 : nat -> Prop) := x0 (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))).
Definition term30 (x0 : nat -> Prop) := @eq Prop ((fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))))).
Definition term0 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term9 (x0 : nat -> Prop) := x0 (minimal x0).
Definition term29 (x0 : nat -> Prop) := fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term27 (x0 : nat -> Prop) := x0 (@ε nat x0).
Definition term28 (x0 : nat -> Prop) := (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)))).
Definition term14 (x0 : nat) (x1 : nat -> Prop) := Peano.lt x0 (@ε nat (fun y0 : nat => (x1 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x1 y1)))).
Definition term7 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (minimal y0) = (@ε nat (fun y1 : nat => (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))))) x0.
Definition term32 := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))).
Definition term20 (x0 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 (minimal x0)) -> ~ (x0 y0).
Definition term5 := forall y0 : nat -> Prop, (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) = (exists y1 : nat, y0 y1).
Definition term4 := forall y0 : nat -> Prop, (exists y1 : nat, y0 y1) = (exists y1 : nat, (y0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))).
Definition term19 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))))) -> ~ (x0 x1).
Definition term24 (x0 : nat -> Prop) := (x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)).
Definition term15 (x0 : nat) (x1 : nat -> Prop) := imp (Peano.lt x0 (minimal x1)).
Definition term1 (x0 : nat -> Prop) := exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1)).
Definition term23 (x0 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 (@ε nat (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))))) -> ~ (x0 y0).
Definition term22 (x0 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0).
Definition term26 (x0 : nat -> Prop) := @eq Prop (exists y0 : nat, x0 y0).
Definition term31 (x0 : nat -> Prop) := @eq Prop ((x0 (@ε nat (fun y0 : nat => (x0 y0) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))))) /\ (forall y0 : nat, (Peano.lt y0 (@ε nat (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))))) -> ~ (x0 y0))).
