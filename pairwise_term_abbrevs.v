Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : type1402 a0) := fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ (~ (y1 = y2)))) -> x0 y1 y2.
Definition term1 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => fun y1 : a0 -> Prop => forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ (~ (y2 = y3)))) -> y0 y2 y3) x0.
Definition term3 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ (~ (y1 = y2)))) -> x0 y1 y2) x1.
Definition term7 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : a0 -> Prop, (@pairwise a0 y0 y1) = (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ (~ (y2 = y3)))) -> y0 y2 y3)) x0.
Definition term10 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : type1402 a0, (@pairwise a0 y1 y0) = (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y0) /\ ((@IN a0 y3 y0) /\ (~ (y2 = y3)))) -> y1 y2 y3).
Definition term6 (a0 : Type') := forall y0 : type1402 a0, forall y1 : a0 -> Prop, (@pairwise a0 y0 y1) = (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ (~ (y2 = y3)))) -> y0 y2 y3).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : type1402 a0) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (~ (y0 = y1)))) -> x1 y0 y1.
Definition term8 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@pairwise a0 x0 y0) = (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ (~ (y1 = y2)))) -> x0 y1 y2)) x1.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type1402 a0, (@pairwise a0 y0 x0) = (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 x0) /\ ((@IN a0 y2 x0) /\ (~ (y1 = y2)))) -> y0 y1 y2).
Definition term5 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (@pairwise a0 x0 y0) = (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ (~ (y1 = y2)))) -> x0 y1 y2).
Definition term0 (a0 : Type') := fun y0 : type1402 a0 => fun y1 : a0 -> Prop => forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ (~ (y2 = y3)))) -> y0 y2 y3.