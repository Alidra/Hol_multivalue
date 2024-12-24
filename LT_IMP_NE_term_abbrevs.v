Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term25 (x0 : nat -> Prop) := ~ (all x0).
Definition term49 := (~ False) -> False.
Definition term4 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term9 := ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term48 (x0 : nat) := (Peano.lt x0 x0) -> False.
Definition term21 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ (~ (~ (x0 = x1))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term33 (x0 : nat) := exists y0 : nat, (Peano.lt x0 y0) /\ (x0 = y0).
Definition term27 (x0 : nat) := ~ (forall y0 : nat, (Peano.lt x0 y0) -> ~ (x0 = y0)).
Definition term3 := ~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1)).
Definition term23 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x0 x1) -> ~ (x0 = x1)).
Definition term47 (x0 : Prop) := (~ x0) -> x0.
Definition term38 := fun y0 : nat => exists y1 : nat, (Peano.lt y0 y1) /\ (y0 = y1).
Definition term45 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term41 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term6 := (((~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term1 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1).
Definition term44 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt y0 x0) x1).
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term32 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) /\ (x0 = y0).
Definition term13 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term2 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> False.
Definition term10 := forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term37 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) -> ~ (y1 = y2)) y0).
Definition term22 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) /\ (x0 = x1).
Definition term8 := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term14 := fun y0 : nat => ~ (Peano.lt y0 y0).
Definition term20 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term17 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> ~ (x0 = y0).
Definition term36 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1)) x0).
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1)) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term34 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) -> ~ (y1 = y2)) y0).
Definition term28 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (Peano.lt x0 y1) -> ~ (x0 = y1)) y0).
Definition term12 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> ~ (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> ~ (x0 = y0)) x1.
Definition term18 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1).
Definition term16 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) -> ~ (x0 = y0).
Definition term39 := exists y0 : nat, exists y1 : nat, (Peano.lt y0 y1) /\ (y0 = y1).
Definition term31 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (Peano.lt x0 y1) -> ~ (x0 = y1)) y0).
Definition term30 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (Peano.lt x0 y0) -> ~ (x0 = y0)) x1).
Definition term5 := ((~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term19 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term7 := (((~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> False.
Definition term15 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ~ (x0 = x1).
Definition term43 (x0 : nat) := (fun y0 : nat => Peano.lt y0 x0) x0.
Definition term26 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term46 (x0 : nat) := (~ (Peano.lt x0 x0)) -> Peano.lt x0 x0.
Definition term11 := imp (~ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1))).
