Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (fun y0 : Prop => (y0 = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 y0 x0 x1) = (@COND a0 x2 x3 x4)) False.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (False = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 False x0 x1) = (@COND a0 x2 x3 x4).
Definition term6 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := @eq Prop ((x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5)).
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) (x5 : Prop) := (fun y0 : Prop => (y0 = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 y0 x0 x1) = (@COND a0 x2 x3 x4)) x5.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) (x5 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 y0 x0 x1) = (@COND a0 x2 x3 x4)) x5).
Definition term5 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) (x3 : a0) (x4 : a0) := fun y0 : Prop => (y0 = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> x1 = x4) -> (@COND a0 y0 x0 x1) = (@COND a0 x2 x3 x4).
