Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := ((~ x2) -> x1 = x4) -> (@COND a0 True x0 x1) = (@COND a0 x2 x3 x4).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 True x0 x1) = (@COND a0 x2 x3 x4).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := ((~ True) -> x0 = x3) -> x1 = (@COND a0 True x2 x3).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := True -> (True -> x1 = x2) -> ((~ True) -> x0 = x3) -> x1 = (@COND a0 True x2 x3).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (True = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 True x0 x1) = (@COND a0 x2 x3 x4).
Definition term0 (x0 : Prop) := imp (True = x0).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (True -> x1 = x2) -> ((~ True) -> x0 = x3) -> x1 = (@COND a0 True x2 x3).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (x2 -> x1 = x3) -> ((~ x2) -> x0 = x4) -> x1 = (@COND a0 x2 x3 x4).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0) := False -> x0 = x1.
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := @eq Prop (x2 -> (x2 -> x1 = x3) -> ((~ x2) -> x0 = x4) -> x1 = (@COND a0 x2 x3 x4)).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (False -> x1 = x2) -> ((~ False) -> x0 = x3) -> x1 = (@COND a0 False x2 x3).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0) := (~ True) -> x0 = x1.
Definition term2 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := imp ((~ x0) -> x1 = x2).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := ((~ x2) -> x0 = x4) -> x1 = (@COND a0 x2 x3 x4).
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 (@COND a0 True x0 x1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := x2 -> (x2 -> x1 = x3) -> ((~ x2) -> x0 = x4) -> x1 = (@COND a0 x2 x3 x4).
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) := imp ((~ True) -> x0 = x1).
Definition term11 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0) := imp (x0 = x1).
Definition term5 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := imp (x0 -> x1 = x2).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => y0 -> (y0 -> x1 = x2) -> ((~ y0) -> x0 = x3) -> x1 = (@COND a0 y0 x2 x3)) x4.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (fun y0 : Prop => y0 -> (y0 -> x1 = x2) -> ((~ y0) -> x0 = x3) -> x1 = (@COND a0 y0 x2 x3)) False.
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0) := True -> x0 = x1.
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0) := imp (True -> x0 = x1).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := False -> (False -> x1 = x2) -> ((~ False) -> x0 = x3) -> x1 = (@COND a0 False x2 x3).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (fun y0 : Prop => y0 -> (y0 -> x1 = x2) -> ((~ y0) -> x0 = x3) -> x1 = (@COND a0 y0 x2 x3)) True.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) -> x0 = x1.
Definition term24 := imp (~ True).
Definition term10 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := fun y0 : Prop => y0 -> (y0 -> x1 = x2) -> ((~ y0) -> x0 = x3) -> x1 = (@COND a0 y0 x2 x3).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) (x4 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> (y0 -> x1 = x2) -> ((~ y0) -> x0 = x3) -> x1 = (@COND a0 y0 x2 x3)) x4).
