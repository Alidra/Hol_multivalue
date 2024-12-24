Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) (x2 : a0) := @COND a1 True (x0 x2) (x1 x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term17 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) := forall y0 : a0 -> a1, (fun y1 : a0 => @COND a1 x0 (x1 y1) (y0 y1)) = (@COND (a0 -> a1) x0 x1 y0).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := @eq (a0 -> a1) (fun y0 : a0 => @COND a1 False (x0 y0) (x1 y0)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := @eq (a0 -> a1) (fun y0 : a0 => @COND a1 True (x0 y0) (x1 y0)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) (x2 : a0 -> a1) := fun y0 : a0 => @COND a1 x0 (x1 y0) (x2 y0).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) (x2 : Prop) := (fun y0 : Prop => (fun y1 : a0 => @COND a1 y0 (x0 y1) (x1 y1)) = (@COND (a0 -> a1) y0 x0 x1)) x2.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := fun y0 : a0 => @COND a1 True (x0 y0) (x1 y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := fun y0 : Prop => (fun y1 : a0 => @COND a1 y0 (x0 y1) (x1 y1)) = (@COND (a0 -> a1) y0 x0 x1).
Definition term10 (a0 : Type') (a1 : Type') (x0 : Prop) (x1 : a0 -> a1) (x2 : a0 -> a1) := @eq Prop ((fun y0 : a0 => @COND a1 x0 (x1 y0) (x2 y0)) = (@COND (a0 -> a1) x0 x1 x2)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) (x2 : a0) := @COND a1 False (x0 x2) (x1 x2).
Definition term3 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term19 (a0 : Type') (a1 : Type') := forall y0 : Prop, forall y1 : a0 -> a1, forall y2 : a0 -> a1, (fun y3 : a0 => @COND a1 y0 (y1 y3) (y2 y3)) = (@COND (a0 -> a1) y0 y1 y2).
Definition term18 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, (fun y2 : a0 => @COND a1 x0 (y0 y2) (y1 y2)) = (@COND (a0 -> a1) x0 y0 y1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := fun y0 : a0 => @COND a1 False (x0 y0) (x1 y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : Prop => (fun y1 : a0 => @COND a1 y0 (x0 y1) (x1 y1)) = (@COND (a0 -> a1) y0 x0 x1)) True.
Definition term2 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : Prop => (fun y1 : a0 => @COND a1 y0 (x0 y1) (x1 y1)) = (@COND (a0 -> a1) y0 x0 x1)) False.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (fun y1 : a0 => @COND a1 y0 (x0 y1) (x1 y1)) = (@COND (a0 -> a1) y0 x0 x1)) x2).
