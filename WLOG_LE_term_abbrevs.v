Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term107 (x0 : type1605) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1)) y0).
Definition term49 (x0 : nat -> Prop) := ~ (all x0).
Definition term184 := (~ False) -> False.
Definition term18 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term21 (x0 : type1605) (x1 : nat) := fun y0 : nat => x0 x1 y0.
Definition term80 (x0 : type1605) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (x0 x1 y0) \/ (~ (x0 y0 x1))) x2).
Definition term90 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 x1 y0) \/ (~ (x0 y0 x1)).
Definition term27 (x0 : type1605) (x1 : nat) := forall y0 : nat, (Peano.le x1 y0) -> x0 x1 y0.
Definition term99 (x0 : type1605) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1)) y0).
Definition term74 (x0 : type1605) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0) /\ ((fun y1 : nat => (~ (x0 x1 y1)) \/ (x0 y1 x1)) y0).
Definition term183 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 x2) -> False.
Definition term148 (x0 : type1605) (x1 : nat) := fun y0 : nat => (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ ((fun y1 : nat => ~ (x0 x1 y1)) y0).
Definition term171 (x0 : Prop) := ~ (~ x0).
Definition term31 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 x1 y0) = (x0 y0 x1).
Definition term85 (x0 : type1605) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0) /\ ((fun y1 : nat => (~ (x0 x1 y1)) \/ (x0 y1 x1)) y0).
Definition term185 (x0 : type1605) := (fun y0 : type1605 => (~ (((forall y1 : nat, forall y2 : nat, (y0 y1 y2) = (y0 y2 y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2)) -> forall y1 : nat, forall y2 : nat, y0 y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False) x0.
Definition term4 (x0 : type1605) := (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term146 (x0 : type1605) (x1 : nat) (x2 : nat) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ ((fun y0 : nat => ~ (x0 x1 y0)) x2).
Definition term79 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x2 x1) \/ (~ (x0 x1 x2)).
Definition term6 (x0 : type1605) := (((~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term124 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term100 (x0 : type1605) := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1)) y0).
Definition term75 (x0 : type1605) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (x0 x1 y1)) \/ (x0 y1 x1)) y0).
Definition term118 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0)).
Definition term48 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, ((x0 y0 y1) \/ (~ (x0 y1 y0))) /\ ((~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)).
Definition term35 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1).
Definition term39 (x0 : type1605) (x1 : nat) := forall y0 : nat, ((x0 x1 y0) \/ (~ (x0 y0 x1))) /\ ((~ (x0 x1 y0)) \/ (x0 y0 x1)).
Definition term62 (x0 : type1605) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, x0 y0 y1) x1).
Definition term140 (x0 : type1605) (x1 : nat) := exists y0 : nat, (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ ((fun y1 : nat => ~ (x0 x1 y1)) y0).
Definition term128 (x0 : type1605) := exists y0 : nat, (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ ((fun y1 : nat => exists y2 : nat, ~ (x0 y1 y2)) y0).
Definition term1 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term94 (x0 : type1605) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (~ (x0 x1 y1)) \/ (x0 y1 x1)) y0.
Definition term89 (x0 : type1605) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0.
Definition term154 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term159 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term72 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term97 (x0 : type1605) := fun y0 : nat => (forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0)).
Definition term59 (x0 : type1605) := ~ (forall y0 : nat, forall y1 : nat, x0 y0 y1).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term123 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term174 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term166 (x0 : Prop) := (~ x0) -> x0.
Definition term181 (x0 : type1605) (x1 : nat) (x2 : nat) := imp (x0 x1 x2).
Definition term64 (x0 : type1605) := fun y0 : nat => exists y1 : nat, ~ (x0 y0 y1).
Definition term84 (x0 : type1605) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (x0 x1 y0) \/ (~ (x0 y0 x1))) x2) /\ ((fun y0 : nat => (~ (x0 x1 y0)) \/ (x0 y0 x1)) x2).
Definition term134 (x0 : type1605) (x1 : nat) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ ((fun y0 : nat => exists y1 : nat, ~ (x0 y0 y1)) x1).
Definition term151 (x0 : type1605) := fun y0 : nat => exists y1 : nat, (((forall y2 : nat, forall y3 : nat, (x0 y2 y3) \/ (~ (x0 y3 y2))) /\ (forall y2 : nat, forall y3 : nat, (~ (x0 y2 y3)) \/ (x0 y3 y2))) /\ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3))) /\ (~ (x0 y0 y1)).
Definition term165 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term179 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (~ (x0 x1 x2)).
Definition term109 (x0 : type1605) := @eq Prop (forall y0 : nat, (forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))).
Definition term108 (x0 : type1605) := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1)) y0)).
Definition term87 (x0 : type1605) (x1 : nat) := @eq Prop (forall y0 : nat, ((x0 x1 y0) \/ (~ (x0 y0 x1))) /\ ((~ (x0 x1 y0)) \/ (x0 y0 x1))).
Definition term86 (x0 : type1605) (x1 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0) /\ ((fun y1 : nat => (~ (x0 x1 y1)) \/ (x0 y1 x1)) y0)).
Definition term141 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ (x0 x1 y0)) x2.
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term149 (x0 : type1605) (x1 : nat) := fun y0 : nat => (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ (~ (x0 x1 y0)).
Definition term130 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ~ (x0 y1 y2)) y0.
Definition term155 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)) x1.
Definition term105 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0)) x1.
Definition term103 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) x1.
Definition term164 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.le x0 x1.
Definition term102 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0).
Definition term45 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1).
Definition term32 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (x0 y0 y1) = (x0 y1 y0).
Definition term28 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term20 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term19 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term120 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1)).
Definition term13 := fun y0 : type1605 => (~ (((forall y1 : nat, forall y2 : nat, (y0 y1 y2) = (y0 y2 y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2)) -> forall y1 : nat, forall y2 : nat, y0 y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term143 (x0 : type1605) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ~ (x0 x1 y1)) y0.
Definition term38 (x0 : type1605) (x1 : nat) := fun y0 : nat => ((x0 x1 y0) \/ (~ (x0 y0 x1))) /\ ((~ (x0 x1 y0)) \/ (x0 y0 x1)).
Definition term126 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term16 := forall y0 : type1605, (~ (((forall y1 : nat, forall y2 : nat, (y0 y1 y2) = (y0 y2 y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2)) -> forall y1 : nat, forall y2 : nat, y0 y1 y2)) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)).
Definition term30 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 y0) = (x0 y0 x1).
Definition term119 (x0 : type1605) := and ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))).
Definition term67 (x0 : type1605) := and ((forall y0 : nat, forall y1 : nat, ((x0 y0 y1) \/ (~ (x0 y1 y0))) /\ ((~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))).
Definition term66 (x0 : type1605) := and ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)).
Definition term156 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x1 y0)) \/ (x0 x1 y0)) x2.
Definition term161 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term88 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0.
Definition term176 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 x2 x1)) \/ (x0 x1 x2)).
Definition term168 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x2)) \/ (x0 x1 x2)).
Definition term125 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term15 := forall y0 : type1605, (~ (((forall y1 : nat, forall y2 : nat, (y0 y1 y2) = (y0 y2 y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2)) -> forall y1 : nat, forall y2 : nat, y0 y1 y2)) -> (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)) -> False.
Definition term8 := (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term82 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 x1 y0)) \/ (x0 y0 x1)) x2.
Definition term92 (x0 : type1605) (x1 : nat) := and (forall y0 : nat, (x0 x1 y0) \/ (~ (x0 y0 x1))).
Definition term36 (x0 : type1605) := imp ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)).
Definition term37 (x0 : type1605) (x1 : nat) (x2 : nat) := ((x0 x2 x1) \/ (~ (x0 x1 x2))) /\ ((~ (x0 x2 x1)) \/ (x0 x1 x2)).
Definition term43 (x0 : type1605) (x1 : nat) := fun y0 : nat => (~ (Peano.le x1 y0)) \/ (x0 x1 y0).
Definition term117 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0).
Definition term112 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0)).
Definition term46 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1).
Definition term41 (x0 : type1605) := forall y0 : nat, forall y1 : nat, ((x0 y0 y1) \/ (~ (x0 y1 y0))) /\ ((~ (x0 y0 y1)) \/ (x0 y1 y0)).
Definition term33 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0).
Definition term29 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1.
Definition term24 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term10 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0).
Definition term138 (x0 : type1605) := exists y0 : nat, (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ (exists y1 : nat, ~ (x0 y0 y1)).
Definition term147 (x0 : type1605) (x1 : nat) (x2 : nat) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (~ (x0 x1 x2)).
Definition term83 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x2 x1)) \/ (x0 x1 x2).
Definition term25 (x0 : type1605) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> x0 x1 x2.
Definition term182 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x2 x1) -> x0 x1 x2.
Definition term53 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 x1 y0) x2.
Definition term68 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) /\ (~ (forall y0 : nat, forall y1 : nat, x0 y0 y1)).
Definition term95 (x0 : type1605) (x1 : nat) := forall y0 : nat, (~ (x0 x1 y0)) \/ (x0 y0 x1).
Definition term63 (x0 : type1605) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, x0 y1 y2) y0).
Definition term44 (x0 : type1605) (x1 : nat) := forall y0 : nat, (~ (Peano.le x1 y0)) \/ (x0 x1 y0).
Definition term17 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term136 (x0 : type1605) := fun y0 : nat => (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ ((fun y1 : nat => exists y2 : nat, ~ (x0 y1 y2)) y0).
Definition term73 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term177 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x2 x1) \/ (~ (x0 x1 x2))).
Definition term55 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ (x0 x1 x2).
Definition term145 (x0 : type1605) (x1 : nat) := @eq Prop ((((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, ~ (x0 x1 y0))).
Definition term144 (x0 : type1605) (x1 : nat) := @eq Prop ((((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, (fun y1 : nat => ~ (x0 x1 y1)) y0)).
Definition term133 (x0 : type1605) := @eq Prop ((((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 y1))).
Definition term132 (x0 : type1605) := @eq Prop ((((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ~ (x0 y1 y2)) y0)).
Definition term104 (x0 : type1605) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) x1).
Definition term76 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 y0) \/ (~ (x0 y0 x1)).
Definition term162 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> ~ (Peano.le x0 x1).
Definition term106 (x0 : type1605) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) x1) /\ ((fun y0 : nat => forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0)) x1).
Definition term96 (x0 : type1605) (x1 : nat) := (forall y0 : nat, (x0 x1 y0) \/ (~ (x0 y0 x1))) /\ (forall y0 : nat, (~ (x0 x1 y0)) \/ (x0 y0 x1)).
Definition term114 (x0 : type1605) := and (forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))).
Definition term47 (x0 : type1605) := and (forall y0 : nat, forall y1 : nat, ((x0 y0 y1) \/ (~ (x0 y1 y0))) /\ ((~ (x0 y0 y1)) \/ (x0 y1 y0))).
Definition term34 (x0 : type1605) := and (forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)).
Definition term175 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 x2)) -> x0 x1 x2.
Definition term137 (x0 : type1605) := fun y0 : nat => (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ (exists y1 : nat, ~ (x0 y0 y1)).
Definition term115 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1)) y0.
Definition term110 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0.
Definition term81 (x0 : type1605) (x1 : nat) (x2 : nat) := and ((x0 x2 x1) \/ (~ (x0 x1 x2))).
Definition term153 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term58 (x0 : type1605) (x1 : nat) := exists y0 : nat, ~ (x0 x1 y0).
Definition term180 (x0 : type1605) (x1 : nat) (x2 : nat) := imp (~ (~ (x0 x1 x2))).
Definition term5 (x0 : type1605) := ((~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term172 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term121 (x0 : type1605) := and (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))).
Definition term56 (x0 : type1605) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => x0 x1 y1) y0).
Definition term178 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (~ (x0 x2 x1))) -> x0 x1 x2.
Definition term170 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x1 x2))) -> x0 x1 x2.
Definition term22 (x0 : type1605) (x1 : nat) := forall y0 : nat, x0 x1 y0.
Definition term60 (x0 : type1605) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, x0 y1 y2) y0).
Definition term52 (x0 : type1605) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => x0 x1 y1) y0).
Definition term69 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, ((x0 y0 y1) \/ (~ (x0 y1 y0))) /\ ((~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 y1)).
Definition term163 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.le x0 x1)).
Definition term139 (x0 : type1605) (x1 : nat) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, (fun y1 : nat => ~ (x0 x1 y1)) y0).
Definition term127 (x0 : type1605) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ~ (x0 y1 y2)) y0).
Definition term167 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 x2) \/ (~ (Peano.le x1 x2)).
Definition term93 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (~ (x0 x1 y1)) \/ (x0 y1 x1)) y0.
Definition term135 (x0 : type1605) (x1 : nat) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, ~ (x0 x1 y0)).
Definition term113 (x0 : type1605) := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0).
Definition term91 (x0 : type1605) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => (x0 x1 y1) \/ (~ (x0 y1 x1))) y0).
Definition term12 (x0 : type1605) := (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> ~ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)).
Definition term142 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ~ (x0 x1 y1)) y0.
Definition term122 (x0 : type1605) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (x0 y0 y1))) /\ (exists y0 : nat, exists y1 : nat, ~ (x0 y0 y1)).
Definition term169 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((x0 x1 x2) \/ (~ (Peano.le x1 x2))).
Definition term54 (x0 : type1605) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => x0 x1 y0) x2).
Definition term160 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (x0 x1 x2)) -> ~ (Peano.le x1 x2).
Definition term101 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0)).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term131 (x0 : type1605) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ~ (x0 y1 y2)) y0.
Definition term152 (x0 : type1605) := exists y0 : nat, exists y1 : nat, (((forall y2 : nat, forall y3 : nat, (x0 y2 y3) \/ (~ (x0 y3 y2))) /\ (forall y2 : nat, forall y3 : nat, (~ (x0 y2 y3)) \/ (x0 y3 y2))) /\ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) \/ (x0 y2 y3))) /\ (~ (x0 y0 y1)).
Definition term65 (x0 : type1605) := exists y0 : nat, exists y1 : nat, ~ (x0 y0 y1).
Definition term57 (x0 : type1605) (x1 : nat) := fun y0 : nat => ~ (x0 x1 y0).
Definition term98 (x0 : type1605) := forall y0 : nat, (forall y1 : nat, (x0 y0 y1) \/ (~ (x0 y1 y0))) /\ (forall y1 : nat, (~ (x0 y0 y1)) \/ (x0 y1 y0)).
Definition term11 (x0 : type1605) := imp (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)).
Definition term77 (x0 : type1605) (x1 : nat) := fun y0 : nat => (~ (x0 x1 y0)) \/ (x0 y0 x1).
Definition term61 (x0 : type1605) (x1 : nat) := (fun y0 : nat => forall y1 : nat, x0 y0 y1) x1.
Definition term26 (x0 : type1605) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) -> x0 x1 y0.
Definition term2 (x0 : type1605) := (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> False.
Definition term51 (x0 : type1605) (x1 : nat) := ~ (forall y0 : nat, x0 x1 y0).
Definition term7 (x0 : type1605) := (((~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> ((~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False) -> (~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1)) -> (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) -> False.
Definition term116 (x0 : type1605) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1)) y0.
Definition term111 (x0 : type1605) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) y0.
Definition term129 (x0 : type1605) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ~ (x0 y0 y1)) x1.
Definition term14 := fun y0 : type1605 => (~ (((forall y1 : nat, forall y2 : nat, (y0 y1 y2) = (y0 y2 y1)) /\ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> y0 y1 y2)) -> forall y1 : nat, forall y2 : nat, y0 y1 y2)) -> ~ (forall y1 : nat, forall y2 : nat, (Peano.le y1 y2) \/ (Peano.le y2 y1)).
Definition term50 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term3 (x0 : type1605) := ~ (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1).
Definition term157 (x0 : type1605) (x1 : nat) (x2 : nat) := (x0 x1 x2) -> ~ (x0 x1 x2).
Definition term40 (x0 : type1605) := fun y0 : nat => forall y1 : nat, ((x0 y0 y1) \/ (~ (x0 y1 y0))) /\ ((~ (x0 y0 y1)) \/ (x0 y1 y0)).
Definition term23 (x0 : type1605) := fun y0 : nat => forall y1 : nat, x0 y0 y1.
Definition term158 (x0 : Prop) := x0 -> ~ x0.
Definition term42 (x0 : type1605) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x2)) \/ (x0 x1 x2).
Definition term150 (x0 : type1605) (x1 : nat) := exists y0 : nat, (((forall y1 : nat, forall y2 : nat, (x0 y1 y2) \/ (~ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (x0 y1 y2)) \/ (x0 y2 y1))) /\ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) \/ (x0 y1 y2))) /\ (~ (x0 x1 y0)).
Definition term78 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 x1 y0) \/ (~ (x0 y0 x1))) x2.
Definition term173 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).