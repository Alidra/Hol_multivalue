Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((@IN a0 x0 x1) -> (((fun y0 : a0 => real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))) = True) -> ((@IN a0 x0 x1) -> ((fun y0 : a0 => real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))) = ((@IN a0 x0 x1) -> True).
Definition term37 (a0 : Type') := fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x0) -> ((fun y1 : a0 => real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) -> (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term12 (a0 : Type') (x0 : a0) := (fun y0 : a0 => real_of_num (NUMERAL 0)) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> (@sum a0 x0 x1) = (real_of_num (NUMERAL 0)).
Definition term5 := real_of_num (NUMERAL 0).
Definition term1 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (real_of_num (NUMERAL 0))) -> (@sum a0 y0 x0) = (real_of_num (NUMERAL 0)).
Definition term34 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term33 (a0 : Type') := forall y0 : a0, True.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term41 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> ((fun y1 : a0 => real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term23 (a0 : Type') (x0 : a0) := @eq real ((fun y0 : a0 => (fun y1 : a0 => real_of_num (NUMERAL 0)) y0) x0).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> (((fun y0 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = True.
Definition term39 (a0 : Type') := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term25 := @eq real (real_of_num (NUMERAL 0)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term31 (a0 : Type') := fun y0 : a0 => True.
Definition term20 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((@IN a0 x1 x0) = x2) -> (x2 -> (((fun y1 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = y0) -> ((@IN a0 x1 x0) -> ((fun y1 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = (x2 -> y0)) x3.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) (x3 : Prop) := ((@IN a0 x1 x0) = x2) -> (x2 -> (((fun y0 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = x3) -> ((@IN a0 x1 x0) -> ((fun y0 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = (x2 -> x3).
Definition term0 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (real_of_num (NUMERAL 0))) -> (@sum a0 y1 y0) = (real_of_num (NUMERAL 0))) x0.
Definition term21 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => real_of_num (NUMERAL 0)) y0) x0.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := forall y0 : Prop, ((@IN a0 x1 x0) = x2) -> (x2 -> (((fun y1 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = y0) -> ((@IN a0 x1 x0) -> ((fun y1 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = (x2 -> y0).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term38 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := @eq real (@sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL 0))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x1 x0) = y0) -> (y0 -> (((fun y2 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = y1) -> ((@IN a0 x1 x0) -> ((fun y2 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = (y0 -> y1).
Definition term10 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ((@IN a0 x0 x1) = (@IN a0 x0 x1)) -> ((@IN a0 x0 x1) -> (((fun y0 : a0 => real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))) = x2) -> ((@IN a0 x0 x1) -> ((fun y0 : a0 => real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))) = ((@IN a0 x0 x1) -> x2).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := @sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL 0)).
Definition term24 (a0 : Type') (x0 : a0) := @eq real ((fun y0 : a0 => real_of_num (NUMERAL 0)) x0).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> ((fun y0 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0)).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> ((fun y1 : a0 => real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term2 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (real_of_num (NUMERAL 0))) -> (@sum a0 y0 x0) = (real_of_num (NUMERAL 0))) x1.
Definition term22 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => real_of_num (NUMERAL 0)) y0.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ((@IN a0 x0 x1) -> (((fun y0 : a0 => real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))) = x2) -> ((@IN a0 x0 x1) -> ((fun y0 : a0 => real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))) = ((@IN a0 x0 x1) -> x2).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x1 x0) = y0) -> (y0 -> (((fun y2 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = y1) -> ((@IN a0 x1 x0) -> ((fun y2 : a0 => real_of_num (NUMERAL 0)) x1) = (real_of_num (NUMERAL 0))) = (y0 -> y1)) x2.
Definition term7 (a0 : Type') := fun y0 : a0 => real_of_num (NUMERAL 0).
Definition term40 (a0 : Type') := forall y0 : a0 -> Prop, True.
