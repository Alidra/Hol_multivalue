Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : Prop -> Prop) := ((~ (exists y0 : Prop, x0 y0)) = (~ ((x0 True) \/ (x0 False)))) -> (exists y0 : Prop, x0 y0) = ((x0 True) \/ (x0 False)).
Definition term23 := @eq Prop (~ False).
Definition term50 (x0 : Prop -> Prop) := (~ (x0 True)) /\ (~ (x0 False)).
Definition term25 (x0 : Prop) := imp (~ x0).
Definition term10 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) x1.
Definition term33 (x0 : Prop -> Prop) := forall y0 : Prop, ~ (x0 y0).
Definition term19 (x0 : Prop) := ~ (~ x0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term51 (x0 : Prop -> Prop) := @eq Prop (~ (exists y0 : Prop, x0 y0)).
Definition term5 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term6 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term44 (x0 : Prop -> Prop) := (fun y0 : Prop => ~ (x0 y0)) True.
Definition term54 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term27 (x0 : Prop) (x1 : Prop) := (((~ x0) = (~ x1)) -> x0 = x1) -> x0 = x1.
Definition term3 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term15 (x0 : Prop) (x1 : Prop) := @eq Prop (((~ x0) = (~ x1)) -> x0 = x1).
Definition term4 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term35 (x0 : Prop -> Prop) := (x0 True) /\ (x0 False).
Definition term38 (x0 : Prop -> Prop) := fun y0 : Prop => ~ (x0 y0).
Definition term49 (x0 : Prop -> Prop) := ~ (x0 False).
Definition term39 (x0 : Prop -> Prop) (x1 : Prop) := (fun y0 : Prop => ~ (x0 y0)) x1.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term48 (x0 : Prop -> Prop) := (fun y0 : Prop => ~ (x0 y0)) False.
Definition term52 (x0 : Prop -> Prop) := @eq Prop ((~ (x0 True)) /\ (~ (x0 False))).
Definition term32 (x0 : Prop -> Prop) := ~ (exists y0 : Prop, x0 y0).
Definition term53 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term22 (x0 : Prop) := (~ (~ x0)) -> x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term12 (x0 : Prop) := ((~ True) = (~ x0)) -> True = x0.
Definition term13 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) x1).
Definition term42 (x0 : Prop -> Prop) := @eq Prop (forall y0 : Prop, (fun y1 : Prop => ~ (x0 y1)) y0).
Definition term43 (x0 : Prop -> Prop) := @eq Prop (forall y0 : Prop, ~ (x0 y0)).
Definition term18 := @eq Prop (~ True).
Definition term26 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term16 (x0 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) False.
Definition term8 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term11 (x0 : Prop) := (fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0) True.
Definition term36 (x0 : Prop -> Prop) := forall y0 : Prop, (fun y1 : Prop => ~ (x0 y1)) y0.
Definition term21 (x0 : Prop) := imp (~ (~ x0)).
Definition term30 (x0 : Prop -> Prop) := exists y0 : Prop, x0 y0.
Definition term46 (x0 : Prop -> Prop) := and ((fun y0 : Prop => ~ (x0 y0)) True).
Definition term37 (x0 : Prop -> Prop) := ((fun y0 : Prop => ~ (x0 y0)) True) /\ ((fun y0 : Prop => ~ (x0 y0)) False).
Definition term34 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.
Definition term14 (x0 : Prop) (x1 : Prop) := ((~ x0) = (~ x1)) -> x0 = x1.
Definition term41 (x0 : Prop -> Prop) := fun y0 : Prop => (fun y1 : Prop => ~ (x0 y1)) y0.
Definition term31 (x0 : Prop -> Prop) := (x0 True) \/ (x0 False).
Definition term24 (x0 : Prop) := imp ((~ False) = (~ x0)).
Definition term20 (x0 : Prop) := imp ((~ True) = (~ x0)).
Definition term55 (x0 : Prop -> Prop) := ~ ((x0 True) \/ (x0 False)).
Definition term9 (x0 : Prop) := fun y0 : Prop => ((~ y0) = (~ x0)) -> y0 = x0.
Definition term40 (x0 : Prop -> Prop) (x1 : Prop) := ~ (x0 x1).
Definition term7 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term45 (x0 : Prop -> Prop) := ~ (x0 True).
Definition term47 (x0 : Prop -> Prop) := and (~ (x0 True)).
Definition term17 (x0 : Prop) := ((~ False) = (~ x0)) -> False = x0.
Definition term28 (x0 : Prop) (x1 : Prop) := (((~ x0) = (~ x1)) -> x0 = x1) -> ((~ x0) = (~ x1)) -> x0 = x1.
