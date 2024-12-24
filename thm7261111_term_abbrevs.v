Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) (x3 : a0 -> Prop) := ((@IN a0 x2 x3) -> (((fun y0 : a0 => x0 y0) x2) = (x1 x2)) = True) -> ((@IN a0 x2 x3) -> ((fun y0 : a0 => x0 y0) x2) = (x1 x2)) = ((@IN a0 x2 x3) -> True).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> ((fun y1 : a0 => x1 y1) y0) = (x2 y0).
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) -> (((fun y0 : a0 => x0 y0) x2) = (x1 x2)) = x4) -> ((@IN a0 x2 x3) -> ((fun y0 : a0 => x0 y0) x2) = (x1 x2)) = ((@IN a0 x2 x3) -> x4).
Definition term16 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real (x0 x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> ((fun y1 : a0 => x1 y1) y0) = (x2 y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (x2 y0).
Definition term24 (a0 : Type') := forall y0 : a0, True.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term15 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real ((fun y0 : a0 => x0 y0) x1).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := ((@IN a0 x3 x0) = x4) -> (x4 -> (((fun y0 : a0 => x1 y0) x3) = (x2 x3)) = x5) -> ((@IN a0 x3 x0) -> ((fun y0 : a0 => x1 y0) x3) = (x2 x3)) = (x4 -> x5).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> (x1 x3) = (x2 x3).
Definition term12 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) = (@IN a0 x2 x3)) -> ((@IN a0 x2 x3) -> (((fun y0 : a0 => x0 y0) x2) = (x1 x2)) = x4) -> ((@IN a0 x2 x3) -> ((fun y0 : a0 => x0 y0) x2) = (x1 x2)) = ((@IN a0 x2 x3) -> x4).
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term22 (a0 : Type') := fun y0 : a0 => True.
Definition term7 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := forall y0 : Prop, ((@IN a0 x3 x0) = x4) -> (x4 -> (((fun y1 : a0 => x1 y1) x3) = (x2 x3)) = y0) -> ((@IN a0 x3 x0) -> ((fun y1 : a0 => x1 y1) x3) = (x2 x3)) = (x4 -> y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> ((fun y0 : a0 => x1 y0) x3) = (x2 x3).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x3 x0) = y0) -> (y0 -> (((fun y2 : a0 => x1 y2) x3) = (x2 x3)) = y1) -> ((@IN a0 x3 x0) -> ((fun y2 : a0 => x1 y2) x3) = (x2 x3)) = (y0 -> y1).
Definition term5 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN a0 x3 x0) = x4) -> (x4 -> (((fun y1 : a0 => x1 y1) x3) = (x2 x3)) = y0) -> ((@IN a0 x3 x0) -> ((fun y1 : a0 => x1 y1) x3) = (x2 x3)) = (x4 -> y0)) x5.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (x2 y0)) x3.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) := (@IN a0 x3 x0) -> (((fun y0 : a0 => x1 y0) x3) = (x2 x3)) = True.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x3 x0) = y0) -> (y0 -> (((fun y2 : a0 => x1 y2) x3) = (x2 x3)) = y1) -> ((@IN a0 x3 x0) -> ((fun y2 : a0 => x1 y2) x3) = (x2 x3)) = (y0 -> y1)) x4.
