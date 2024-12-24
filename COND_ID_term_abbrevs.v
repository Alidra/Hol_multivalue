Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (x0 : Prop) := forall y0 : a0, (@COND a0 x0 y0 y0) = y0.
Definition term8 (a0 : Type') (x0 : a0) := @eq a0 (@COND a0 True x0 x0).
Definition term7 (a0 : Type') (x0 : a0) := (fun y0 : Prop => (@COND a0 y0 x0 x0) = x0) False.
Definition term9 (a0 : Type') (x0 : a0) := @eq a0 (@COND a0 False x0 x0).
Definition term4 (a0 : Type') (x0 : a0) := (fun y0 : Prop => (@COND a0 y0 x0 x0) = x0) True.
Definition term3 (a0 : Type') (x0 : a0) (x1 : Prop) := (fun y0 : Prop => (@COND a0 y0 x0 x0) = x0) x1.
Definition term2 (a0 : Type') (x0 : a0) := fun y0 : Prop => (@COND a0 y0 x0 x0) = x0.
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term11 (a0 : Type') := forall y0 : Prop, forall y1 : a0, (@COND a0 y0 y1 y1) = y1.
Definition term6 (a0 : Type') (x0 : Prop) (x1 : a0) := @eq Prop ((@COND a0 x0 x1 x1) = x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term5 (a0 : Type') (x0 : a0) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (@COND a0 y0 x0 x0) = x0) x1).
