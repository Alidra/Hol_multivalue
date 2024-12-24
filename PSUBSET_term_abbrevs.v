Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (~ (x0 = x1)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@PSUBSET a0 x0 y0) = ((@SUBSET a0 x0 y0) /\ (~ (x0 = y0))).
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@SUBSET a0 y0 y1) /\ (~ (y0 = y1)).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@PSUBSET a0 x0 y0) = ((@SUBSET a0 x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) /\ (~ (x0 = y0))) x1.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@SUBSET a0 y0 y1) /\ (~ (y0 = y1))) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) /\ (~ (x0 = y0)).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@PSUBSET a0 y0 y1) = ((@SUBSET a0 y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term6 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@PSUBSET a0 y0 y1) = ((@SUBSET a0 y0 y1) /\ (~ (y0 = y1))).
