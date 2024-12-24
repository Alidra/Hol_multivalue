Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term49 (a0 : Type') := forall y0 : a0, @ex1 (unit -> a0) (fun y1 : unit -> a0 => (y1 tt) = y0).
Definition term27 (a0 : Type') (x0 : unit -> a0) (x1 : a0) (x2 : unit -> a0) := imp (((fun y0 : unit -> a0 => (y0 tt) = x1) x0) /\ ((fun y0 : unit -> a0 => (y0 tt) = x1) x2)).
Definition term22 (a0 : Type') (x0 : a0) := and (exists y0 : unit -> a0, (y0 tt) = x0).
Definition term25 (a0 : Type') (x0 : unit -> a0) (x1 : a0) (x2 : unit -> a0) := ((fun y0 : unit -> a0 => (y0 tt) = x1) x0) /\ ((fun y0 : unit -> a0 => (y0 tt) = x1) x2).
Definition term47 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term41 (a0 : Type') (x0 : unit -> a0) (x1 : unit -> a0) := forall y0 : unit, (x0 y0) = (x1 y0).
Definition term17 (a0 : Type') (x0 : a0) := @ex1 (unit -> a0) (fun y0 : unit -> a0 => (y0 tt) = x0).
Definition term11 (a0 : Type') (x0 : type388 a0) := (exists y0 : unit -> a0, x0 y0) /\ (forall y0 : unit -> a0, forall y1 : unit -> a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, x0 y0) /\ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1).
Definition term13 (a0 : Type') (x0 : a0) := (exists y0 : unit -> a0, (fun y1 : unit -> a0 => (y1 tt) = x0) y0) /\ (forall y0 : unit -> a0, forall y1 : unit -> a0, (((fun y2 : unit -> a0 => (y2 tt) = x0) y0) /\ ((fun y2 : unit -> a0 => (y2 tt) = x0) y1)) -> y0 = y1).
Definition term14 (a0 : Type') (x0 : a0) := fun y0 : unit -> a0 => (y0 tt) = x0.
Definition term18 (a0 : Type') (x0 : a0) := @eq Prop (@ex1 (unit -> a0) (fun y0 : unit -> a0 => (fun y1 : unit -> a0 => (y1 tt) = x0) y0)).
Definition term15 (a0 : Type') (x0 : a0) (x1 : unit -> a0) := (fun y0 : unit -> a0 => (y0 tt) = x0) x1.
Definition term46 (a0 : Type') (x0 : unit -> a0) (x1 : unit -> a0) := forall y0 : unit, (x0 tt) = (x1 tt).
Definition term29 (a0 : Type') (x0 : a0) (x1 : unit -> a0) (x2 : unit -> a0) := (((fun y0 : unit -> a0 => (y0 tt) = x0) x1) /\ ((fun y0 : unit -> a0 => (y0 tt) = x0) x2)) -> x1 = x2.
Definition term12 (a0 : Type') (x0 : a0) := @ex1 (unit -> a0) (fun y0 : unit -> a0 => (fun y1 : unit -> a0 => (y1 tt) = x0) y0).
Definition term36 (a0 : Type') (x0 : a0) := fun y0 : unit -> a0 => forall y1 : unit -> a0, (((y0 tt) = x0) /\ ((y1 tt) = x0)) -> y0 = y1.
Definition term35 (a0 : Type') (x0 : a0) := fun y0 : unit -> a0 => forall y1 : unit -> a0, (((fun y2 : unit -> a0 => (y2 tt) = x0) y0) /\ ((fun y2 : unit -> a0 => (y2 tt) = x0) y1)) -> y0 = y1.
Definition term0 (x0 : unit) := (fun y0 : unit => y0 = tt) x0.
Definition term10 (a0 : Type') (x0 : type388 a0) := @ex1 (unit -> a0) (fun y0 : unit -> a0 => x0 y0).
Definition term48 (x0 : Prop) := forall y0 : unit, x0.
Definition term23 (a0 : Type') (x0 : a0) (x1 : unit -> a0) := and ((fun y0 : unit -> a0 => (y0 tt) = x0) x1).
Definition term5 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : unit -> a0, (y1 tt) = y0) x0.
Definition term21 (a0 : Type') (x0 : a0) := and (exists y0 : unit -> a0, (fun y1 : unit -> a0 => (y1 tt) = x0) y0).
Definition term43 (a0 : Type') (x0 : unit -> a0) := @eq a0 (x0 tt).
Definition term44 (a0 : Type') (x0 : unit -> a0) (x1 : unit -> a0) := fun y0 : unit => (x0 y0) = (x1 y0).
Definition term26 (a0 : Type') (x0 : unit -> a0) (x1 : unit -> a0) (x2 : a0) := ((x0 tt) = x2) /\ ((x1 tt) = x2).
Definition term39 (a0 : Type') (x0 : a0) := (exists y0 : unit -> a0, (y0 tt) = x0) /\ (forall y0 : unit -> a0, forall y1 : unit -> a0, (((y0 tt) = x0) /\ ((y1 tt) = x0)) -> y0 = y1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@ex1 a0 (fun y1 : a0 => y0 y1)) = ((exists y1 : a0, y0 y1) /\ (forall y1 : a0, forall y2 : a0, ((y0 y1) /\ (y0 y2)) -> y1 = y2))) x0.
Definition term6 (a0 : Type') (x0 : a0) := exists y0 : unit -> a0, (y0 tt) = x0.
Definition term31 (a0 : Type') (x0 : a0) (x1 : unit -> a0) := fun y0 : unit -> a0 => (((fun y1 : unit -> a0 => (y1 tt) = x0) x1) /\ ((fun y1 : unit -> a0 => (y1 tt) = x0) y0)) -> x1 = y0.
Definition term40 (a0 : Type') (x0 : a0) := True /\ (forall y0 : unit -> a0, forall y1 : unit -> a0, (((y0 tt) = x0) /\ ((y1 tt) = x0)) -> y0 = y1).
Definition term24 (a0 : Type') (x0 : unit -> a0) (x1 : a0) := and ((x0 tt) = x1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := @ex1 a0 (fun y0 : a0 => x0 y0).
Definition term38 (a0 : Type') (x0 : a0) := forall y0 : unit -> a0, forall y1 : unit -> a0, (((y0 tt) = x0) /\ ((y1 tt) = x0)) -> y0 = y1.
Definition term37 (a0 : Type') (x0 : a0) := forall y0 : unit -> a0, forall y1 : unit -> a0, (((fun y2 : unit -> a0 => (y2 tt) = x0) y0) /\ ((fun y2 : unit -> a0 => (y2 tt) = x0) y1)) -> y0 = y1.
Definition term42 (a0 : Type') (x0 : unit -> a0) (x1 : unit) := @eq a0 (x0 x1).
Definition term45 (a0 : Type') (x0 : unit -> a0) (x1 : unit -> a0) := fun y0 : unit => (x0 tt) = (x1 tt).
Definition term16 (a0 : Type') (x0 : a0) := fun y0 : unit -> a0 => (fun y1 : unit -> a0 => (y1 tt) = x0) y0.
Definition term34 (a0 : Type') (x0 : a0) (x1 : unit -> a0) := forall y0 : unit -> a0, (((x1 tt) = x0) /\ ((y0 tt) = x0)) -> x1 = y0.
Definition term33 (a0 : Type') (x0 : a0) (x1 : unit -> a0) := forall y0 : unit -> a0, (((fun y1 : unit -> a0 => (y1 tt) = x0) x1) /\ ((fun y1 : unit -> a0 => (y1 tt) = x0) y0)) -> x1 = y0.
Definition term30 (a0 : Type') (x0 : a0) (x1 : unit -> a0) (x2 : unit -> a0) := (((x1 tt) = x0) /\ ((x2 tt) = x0)) -> x1 = x2.
Definition term32 (a0 : Type') (x0 : a0) (x1 : unit -> a0) := fun y0 : unit -> a0 => (((x1 tt) = x0) /\ ((y0 tt) = x0)) -> x1 = y0.
Definition term20 (a0 : Type') (x0 : a0) := exists y0 : unit -> a0, (fun y1 : unit -> a0 => (y1 tt) = x0) y0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term28 (a0 : Type') (x0 : unit -> a0) (x1 : unit -> a0) (x2 : a0) := imp (((x0 tt) = x2) /\ ((x1 tt) = x2)).
Definition term19 (a0 : Type') (x0 : a0) := @eq Prop (@ex1 (unit -> a0) (fun y0 : unit -> a0 => (y0 tt) = x0)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
