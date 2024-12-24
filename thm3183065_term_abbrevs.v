Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@SETSPEC a0 x1 x0 y0) = (x0 /\ (x1 = y0))) x2.
Definition term2 (a0 : Type') (x0 : Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@SETSPEC a0 y0 x0 y1) = (x0 /\ (y0 = y1))) x1.
Definition term3 (a0 : Type') (x0 : Prop) (x1 : a0) := forall y0 : a0, (@SETSPEC a0 x1 x0 y0) = (x0 /\ (x1 = y0)).
Definition term1 (a0 : Type') (x0 : Prop) := forall y0 : a0, forall y1 : a0, (@SETSPEC a0 y0 x0 y1) = (x0 /\ (y0 = y1)).
Definition term0 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (@SETSPEC a0 y1 y0 y2) = (y0 /\ (y1 = y2))) x0.
