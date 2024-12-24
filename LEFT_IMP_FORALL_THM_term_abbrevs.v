Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ~ ((forall y0 : a0, x0 y0) -> x1).
Definition term26 := @eq Prop (~ False).
Definition term15 (x0 : Prop) := fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0)).
Definition term24 (x0 : Prop) := @eq Prop (False = x0).
Definition term23 (x0 : Prop) := ~ (~ x0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) -> x1.
Definition term21 (x0 : Prop) := @eq Prop (True = x0).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := @eq Prop (~ (exists y0 : a0, (x0 y0) -> x1)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := @eq Prop (~ (exists y0 : a0, (fun y1 : a0 => (x0 y1) -> x1) y0)).
Definition term6 (x0 : Prop) := forall y0 : Prop, (~ (x0 -> y0)) = (x0 /\ (~ y0)).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) -> x1) x2.
Definition term19 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = x1) = ((~ x0) = (~ x1))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, x0 y0.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (x0 x1) /\ (~ x2).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) /\ x1.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) -> x1.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ~ (exists y0 : a0, (x0 y0) -> x1).
Definition term16 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1.
Definition term5 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (~ (y0 -> y1)) = (y0 /\ (~ y1))) x0.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((forall y1 : a0, x0 y1) -> y0) = (exists y1 : a0, (x0 y1) -> y0).
Definition term20 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) False.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := @eq Prop (forall y0 : a0, (x0 y0) /\ (~ x1)).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) := ~ ((fun y0 : a0 => (x0 y0) -> x1) x2).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ~ (exists y0 : a0, (fun y1 : a0 => (x0 y1) -> x1) y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => (x0 y0) -> x1.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((forall y1 : a0, x0 y1) /\ y0) = (forall y1 : a0, (x0 y1) /\ y0)) x1.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term25 (x0 : Prop) := @eq Prop (~ x0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (fun y1 : a0 => (x0 y1) -> x1) y0.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => (x0 y0) /\ (~ x1).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => (fun y1 : a0 => (x0 y1) -> x1) y0.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := @eq Prop (~ ((forall y0 : a0, x0 y0) -> x1)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := ~ ((x0 x1) -> x2).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((forall y2 : a0, y0 y2) /\ y1) = (forall y2 : a0, (y0 y2) /\ y1)) x0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term18 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1).
Definition term22 := @eq Prop (~ True).
Definition term14 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term53 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : Prop, ((forall y2 : a0, y0 y2) -> y1) = (exists y2 : a0, (y0 y2) -> y1).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (x0 x1) -> x2.
Definition term7 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (x0 -> y0)) = (x0 /\ (~ y0))) x1.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => (x0 y1) -> x1) y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((forall y1 : a0, x0 y1) /\ y0) = (forall y1 : a0, (x0 y1) /\ y0).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) /\ (~ x1).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) /\ (~ x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) /\ x1.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, ~ ((x0 y0) -> x1).
Definition term9 (x0 : Prop) (x1 : Prop) := x0 /\ (~ x1).
Definition term8 (x0 : Prop) (x1 : Prop) := ~ (x0 -> x1).
Definition term17 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) True.
Definition term13 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, ~ ((fun y1 : a0 => (x0 y1) -> x1) y0).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := fun y0 : a0 => ~ ((x0 y0) -> x1).
