Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 := @eq Prop (~ False).
Definition term20 (a0 : Type') (x0 : type1402 a0) := ~ (@WF a0 x0).
Definition term28 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2))) x1.
Definition term2 (x0 : Prop) := fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0).
Definition term11 (x0 : Prop) := ~ (~ x0).
Definition term7 (x0 : Prop) := (fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) False.
Definition term8 (x0 : Prop) := @eq Prop (True = (~ x0)).
Definition term22 (a0 : Type') (x0 : type1402 a0) := ~ (forall y0 : a0 -> Prop, (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2))).
Definition term19 (a0 : Type') (x0 : type1402 a0) := ~ (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)).
Definition term12 (x0 : Prop) := @eq Prop (False = (~ x0)).
Definition term29 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (exists y0 : a0, x1 y0) -> exists y0 : a0, (x1 y0) /\ (forall y1 : a0, (x0 y1 y0) -> ~ (x1 y1)).
Definition term35 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := ~ ((exists y0 : a0, x1 y0) -> exists y0 : a0, (x1 y0) /\ (forall y1 : a0, (x0 y1 y0) -> ~ (x1 y1))).
Definition term34 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2))) x1).
Definition term21 (a0 : Type') (x0 : type1402 a0) := exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term37 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 -> Prop => ~ ((exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, y0 y1)) = (exists y1 : a0, ~ (y0 y1))) x0.
Definition term39 (a0 : Type') (x0 : type1402 a0) := @eq Prop (~ (@WF a0 x0)).
Definition term23 (a0 : Type') (x0 : type686 a0) := ~ (forall y0 : a0 -> Prop, x0 y0).
Definition term26 (a0 : Type') (x0 : type1402 a0) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (x0 y3 y2) -> ~ (y1 y3))) y0).
Definition term9 (x0 : Prop) := @eq Prop (~ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) x1.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term31 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (x0 y3 y2) -> ~ (y1 y3))) y0.
Definition term36 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (x0 y3 y2) -> ~ (y1 y3))) y0).
Definition term17 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => (@WF a0 y0) = (forall y1 : a0 -> Prop, (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (y0 y3 y2) -> ~ (y1 y3)))) x0.
Definition term27 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 -> Prop => (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2)).
Definition term5 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) x1).
Definition term10 := @eq Prop (~ True).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term24 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term38 (a0 : Type') (x0 : type1402 a0) := exists y0 : a0 -> Prop, ~ ((exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2))).
Definition term18 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2)).
Definition term33 (a0 : Type') (x0 : type1402 a0) := @eq Prop (~ (forall y0 : a0 -> Prop, (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2)))).
Definition term32 (a0 : Type') (x0 : type1402 a0) := @eq Prop (~ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (x0 y3 y2) -> ~ (y1 y3))) y0)).
Definition term4 (x0 : Prop) := (fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) True.
Definition term30 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (x0 y3 y2) -> ~ (y1 y3))) y0.
Definition term6 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = (~ x1)) = ((~ x0) = x1)).
Definition term40 (a0 : Type') (x0 : type1402 a0) := @eq Prop (exists y0 : a0 -> Prop, ~ ((exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2)))).
Definition term25 (a0 : Type') (x0 : type1402 a0) := ~ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (x0 y3 y2) -> ~ (y1 y3))) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
