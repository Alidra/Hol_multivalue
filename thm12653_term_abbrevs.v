Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, ((@COND a0 True x0 y0) = x0) /\ ((@COND a0 False x0 y0) = y0).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, ((@COND a0 True y0 y1) = y0) /\ ((@COND a0 False y0 y1) = y1)) x0.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) := ((@COND a0 True x0 x1) = x0) /\ ((@COND a0 False x0 x1) = x1).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ((@COND a0 True x0 y0) = x0) /\ ((@COND a0 False x0 y0) = y0)) x1.
