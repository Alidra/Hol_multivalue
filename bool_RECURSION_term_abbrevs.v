Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := exists y0 : Prop -> a0, ((y0 False) = x0) /\ ((y0 True) = x1).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 ((fun y0 : Prop => (fun y1 : Prop => @COND a0 y1 x0 x1) y0) True).
Definition term1 (a0 : Type') (x0 : Prop -> a0) (x1 : Prop) := (fun y0 : Prop => x0 y0) x1.
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 ((fun y0 : Prop => @COND a0 y0 x0 x1) True).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 ((fun y0 : Prop => (fun y1 : Prop => @COND a0 y1 x0 x1) y0) False).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => @COND a0 y0 x0 x1) True.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : Prop => @COND a0 y0 x0 x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 ((fun y0 : Prop => @COND a0 y0 x0 x1) False).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => (fun y1 : Prop => @COND a0 y1 x0 x1) y0) True.
Definition term18 (a0 : Type') := forall y0 : a0, forall y1 : a0, exists y2 : Prop -> a0, ((y2 False) = y0) /\ ((y2 True) = y1).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := (((fun y0 : Prop => @COND a0 y0 x1 x0) False) = x0) /\ (((fun y0 : Prop => @COND a0 y0 x1 x0) True) = x1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) := and (((fun y0 : Prop => @COND a0 y0 x0 x1) False) = x1).
Definition term17 (a0 : Type') (x0 : a0) := forall y0 : a0, exists y1 : Prop -> a0, ((y1 False) = x0) /\ ((y1 True) = y0).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : Prop => (fun y1 : Prop => @COND a0 y1 x0 x1) y0.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (fun y0 : Prop => @COND a0 y0 x0 x1) x2.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => (fun y1 : Prop => @COND a0 y1 x0 x1) y0) False.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : Prop -> a0 => ((y0 False) = x0) /\ ((y0 True) = x1).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : Prop => @COND a0 y0 x0 x1) False.
