Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop (x0 (@COND a0 False x1 x2)).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop (x0 (@COND a0 True x1 x2)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (True -> x0 x1).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ False) -> x0 x1.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = ((y0 -> x1 x0) /\ ((~ y0) -> x1 x2))) x3.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = ((y0 -> x1 x0) /\ ((~ y0) -> x1 x2)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := x0 (@COND a0 True x1 x2).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := x0 (@COND a0 False x1 x2).
Definition term9 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ True) -> x0 x1.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = ((y0 -> x1 x0) /\ ((~ y0) -> x1 x2))) True.
Definition term10 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop ((x2 (@COND a0 x1 x0 x3)) = ((x1 -> x2 x0) /\ ((~ x1) -> x2 x3))).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = ((y0 -> x1 x0) /\ ((~ y0) -> x1 x2))) False.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) (x3 : a0) := x0 (@COND a0 x1 x2 x3).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (True -> x1 x0) /\ ((~ True) -> x1 x2).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True /\ (x0 x1).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term25 := imp (~ False).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (False -> x0 x1).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := @eq Prop ((fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = ((y0 -> x1 x0) /\ ((~ y0) -> x1 x2))) x3).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := True -> x0 x1.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := False -> x0 x1.
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (False -> x1 x0) /\ ((~ False) -> x1 x2).
Definition term19 := imp (~ True).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) /\ True.
