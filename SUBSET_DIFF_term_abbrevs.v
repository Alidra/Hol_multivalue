Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, @SUBSET a0 (@DIFF a0 y0 y1) y0.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term41 := (~ False) -> False.
Definition term36 (x0 : Prop) := ~ (~ x0).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) -> x1 x2.
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2.
Definition term10 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@DIFF a0 y0 y1)) -> @IN a0 y2 y0.
Definition term29 (x0 : Prop) := (~ x0) -> False.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) /\ (~ (x0 y0))) -> x1 y0.
Definition term9 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, @SUBSET a0 (@DIFF a0 y0 y1) y0.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term31 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2).
Definition term39 (x0 : Prop) := (~ x0) -> x0.
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @SUBSET a0 (@DIFF a0 x1 x0) x1.
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> False.
Definition term32 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, @SUBSET a0 (@DIFF a0 x0 y0) x0.
Definition term35 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)).
Definition term30 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 (@DIFF a0 x2 x0)) -> @IN a0 x1 x2.
Definition term33 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@DIFF a0 x1 x0)) -> @IN a0 y0 x1.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := imp ((x0 x2) /\ (~ (x1 x2))).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@DIFF a0 x0 y0)) -> @IN a0 y1 x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @SUBSET a0 (@DIFF a0 x0 y0) x0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@DIFF a0 x1 x0)) -> @IN a0 y0 x1.
Definition term27 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2.
Definition term8 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@DIFF a0 y0 y1)) -> @IN a0 y2 y0.
Definition term34 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@DIFF a0 x0 y0)) -> @IN a0 y1 x0.
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1.
