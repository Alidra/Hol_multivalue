Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, forall y2 : a1, ((@pair a0 a1 x0 y0) = (@pair a0 a1 y1 y2)) = ((x0 = y1) /\ (y0 = y2))) x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, forall y2 : a0, forall y3 : a1, ((@pair a0 a1 y0 y1) = (@pair a0 a1 y2 y3)) = ((y0 = y2) /\ (y1 = y3))) x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (fun y0 : a1 => ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, forall y1 : a0, forall y2 : a1, ((@pair a0 a1 x0 y0) = (@pair a0 a1 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0, forall y1 : a1, ((@pair a0 a1 x0 x1) = (@pair a0 a1 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) := forall y0 : a1, ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) := (fun y0 : a0 => forall y1 : a1, ((@pair a0 a1 x0 x1) = (@pair a0 a1 y0 y1)) = ((x0 = y0) /\ (x1 = y1))) x2.
