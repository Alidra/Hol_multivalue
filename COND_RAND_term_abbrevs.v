Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0) := @eq a1 (x0 (@COND a0 False x1 x2)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0) := @eq a1 (x0 (@COND a0 True x1 x2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0) := x0 (@COND a0 True x1 x2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = (@COND a1 y0 (x1 x0) (x1 x2))) True.
Definition term17 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> a1) := forall y0 : a0, (x2 (@COND a0 x0 x1 y0)) = (@COND a1 x0 (x2 x1) (x2 y0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = (@COND a1 y0 (x1 x0) (x1 x2)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := @COND a1 False (x1 x0) (x1 x2).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := @eq a1 (x0 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : Prop) (x2 : a0) (x3 : a0) := x0 (@COND a0 x1 x2 x3).
Definition term9 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> a1) (x3 : a0) := @COND a1 x0 (x2 x1) (x2 x3).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = (@COND a1 y0 (x1 x0) (x1 x2))) False.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = (@COND a1 y0 (x1 x0) (x1 x2))) x3.
Definition term10 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0) (x2 : a0 -> a1) (x3 : a0) := @eq Prop ((x2 (@COND a0 x0 x1 x3)) = (@COND a1 x0 (x2 x1) (x2 x3))).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term20 (a0 : Type') (a1 : Type') := forall y0 : Prop, forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a0, (y1 (@COND a0 y0 y2 y3)) = (@COND a1 y0 (y1 y2) (y1 y3)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) (x3 : Prop) := @eq Prop ((fun y0 : Prop => (x1 (@COND a0 y0 x0 x2)) = (@COND a1 y0 (x1 x0) (x1 x2))) x3).
Definition term18 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a0, (x1 (@COND a0 x0 y0 y1)) = (@COND a1 x0 (x1 y0) (x1 y1)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : a0, (y0 (@COND a0 x0 y1 y2)) = (@COND a1 x0 (y0 y1) (y0 y2)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> a1) (x2 : a0) := @COND a1 True (x1 x0) (x1 x2).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) (x2 : a0) := x0 (@COND a0 False x1 x2).
