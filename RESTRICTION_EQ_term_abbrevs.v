Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := ((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = True.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : Prop) (x5 : Prop) := (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) = x4) -> (x4 -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = x5) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (x4 -> x5).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = True) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> True).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (@IN a0 x2 x0) -> (@RESTRICTION a0 a1 x0 x1 x2) = (x1 x2).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := ((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> True.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => forall y1 : a0, forall y2 : a1, ((@IN a0 y1 x0) /\ ((y0 y1) = y2)) -> (@RESTRICTION a0 a1 x0 y0 y1) = y2.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (@IN a0 y1 x0) -> (@RESTRICTION a0 a1 x0 y0 y1) = (y0 y1)) x1.
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term36 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a1, ((@IN a0 y2 y0) /\ ((y1 y2) = y3)) -> (@RESTRICTION a0 a1 y0 y1 y2) = y3.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := forall y0 : a1, ((@IN a0 x2 x0) /\ ((x1 x2) = y0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (@IN a0 y0 x0) -> (@RESTRICTION a0 a1 x0 x1 y0) = (x1 y0).
Definition term25 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, (@IN a0 y2 y0) -> (@RESTRICTION a0 a1 y0 y1 y2) = (y1 y2)) x0.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := ((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term33 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : Prop) := (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) = ((@IN a0 x2 x0) /\ ((x1 x2) = x3))) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = x4) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> x4).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> (@RESTRICTION a0 a1 x0 x1 y0) = (x1 y0)) x2.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 => forall y1 : a1, ((@IN a0 y0 x0) /\ ((x1 y0) = y1)) -> (@RESTRICTION a0 a1 x0 x1 y0) = y1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := fun y0 : a1 => ((@IN a0 x2 x0) /\ ((x1 x2) = y0)) -> (@RESTRICTION a0 a1 x0 x1 x2) = y0.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term23 (a0 : Type') := fun y0 : a0 => True.
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 (@RESTRICTION a0 a1 x0 x1 x2).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := (@IN a0 x2 x0) /\ ((x1 x2) = x3).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : Prop) := forall y0 : Prop, (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) = x4) -> (x4 -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = y0) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (x4 -> y0).
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term30 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term35 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) := forall y0 : Prop, forall y1 : Prop, (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) = y0) -> (y0 -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = y1) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (y0 -> y1).
Definition term8 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) = x4) -> (x4 -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = y0) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (x4 -> y0)) x5.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a1, ((@IN a0 y0 x0) /\ ((x1 y0) = y1)) -> (@RESTRICTION a0 a1 x0 x1 y0) = y1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : a1, ((@IN a0 y1 x0) /\ ((y0 y1) = y2)) -> (@RESTRICTION a0 a1 x0 y0 y1) = y2.
Definition term34 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, forall y3 : a1, ((@IN a0 y2 y0) /\ ((y1 y2) = y3)) -> (@RESTRICTION a0 a1 y0 y1 y2) = y3.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) = y0) -> (y0 -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = y1) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (y0 -> y1)) x4.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) (x3 : a1) (x4 : Prop) := (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> ((@RESTRICTION a0 a1 x0 x1 x2) = x3) = x4) -> (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> (@RESTRICTION a0 a1 x0 x1 x2) = x3) = (((@IN a0 x2 x0) /\ ((x1 x2) = x3)) -> x4).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, (@IN a0 y1 x0) -> (@RESTRICTION a0 a1 x0 y0 y1) = (y0 y1).
Definition term37 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term32 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
