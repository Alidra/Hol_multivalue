Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term13 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) = ((Peano.le x0 y0) /\ (~ (x0 = y0))).
Definition term28 (x0 : nat) := (Peano.lt x0 x0) -> False.
Definition term29 (x0 : nat) (x1 : nat) := (x0 = x1) -> False.
Definition term11 (x0 : nat) (x1 : nat) := ((Peano.lt x0 x1) \/ (x0 = x1)) /\ (~ (x0 = x1)).
Definition term34 (x0 : nat) (x1 : nat) := (((Peano.lt x0 x1) \/ (x0 = x1)) /\ (~ (x0 = x1))) -> Peano.lt x0 x1.
Definition term21 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term12 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term24 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term14 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) = (((Peano.lt x0 y0) \/ (x0 = y0)) /\ (~ (x0 = y0))).
Definition term2 (x0 : nat) := (~ (Peano.lt x0 x0)) -> (Peano.lt x0 x0) = False.
Definition term20 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) = (((Peano.lt y0 y1) \/ (y0 = y1)) /\ (~ (y0 = y1))).
Definition term19 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) = ((Peano.le y0 y1) /\ (~ (y0 = y1))).
Definition term10 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) /\ (~ (x0 = x1)).
Definition term27 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt y0 x0) x1).
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term8 (x0 : nat) (x1 : nat) := and ((Peano.lt x0 x1) \/ (x0 = x1)).
Definition term1 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term6 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) \/ (x0 = x1).
Definition term16 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (((Peano.lt x0 y0) \/ (x0 = y0)) /\ (~ (x0 = y0))).
Definition term15 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = ((Peano.le x0 y0) /\ (~ (x0 = y0))).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = ((Peano.lt y0 y1) \/ (y0 = y1))) x0.
Definition term31 (x0 : nat) (x1 : nat) := imp (~ (x0 = x1)).
Definition term23 (x0 : nat) (x1 : nat) := True /\ (~ (x0 = x1)).
Definition term0 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = ((Peano.lt x0 y0) \/ (x0 = y0)).
Definition term32 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> Peano.lt x0 x1.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = ((Peano.lt x0 y0) \/ (x0 = y0))) x1.
Definition term22 (x0 : nat) (x1 : nat) := True \/ (x0 = x1).
Definition term33 (x0 : nat) := False -> Peano.lt x0 x0.
Definition term26 (x0 : nat) := (fun y0 : nat => Peano.lt y0 x0) x0.
Definition term35 (x0 : nat) (x1 : nat) := ((Peano.lt x0 x1) -> ((Peano.lt x0 x1) \/ (x0 = x1)) /\ (~ (x0 = x1))) /\ ((((Peano.lt x0 x1) \/ (x0 = x1)) /\ (~ (x0 = x1))) -> Peano.lt x0 x1).
Definition term30 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ((Peano.lt x0 x1) \/ (x0 = x1)) /\ (~ (x0 = x1)).
Definition term18 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (((Peano.lt y0 y1) \/ (y0 = y1)) /\ (~ (y0 = y1))).
Definition term17 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = ((Peano.le y0 y1) /\ (~ (y0 = y1))).
Definition term7 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
