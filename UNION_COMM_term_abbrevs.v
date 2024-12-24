Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) \/ (x0 x2)) /\ (~ ((x0 x2) \/ (x1 x2)))).
Definition term51 := (~ False) -> False.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 x1 x2)).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x0 x2) \/ (x1 x2))).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) \/ (x0 x2)) /\ ((~ (x0 x2)) /\ (~ (x1 x2))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term31 (x0 : Prop) := ~ (~ x0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) \/ (x0 y0)) = ((x0 y0) \/ (x1 y0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) \/ (x1 x2)).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term23 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)).
Definition term9 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@UNION a0 y0 y1)) = (@IN a0 y2 (@UNION a0 y1 y0)).
Definition term24 (x0 : Prop) := (~ x0) -> False.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x1 x2) \/ (x0 x2)) = ((x0 x2) \/ (x1 x2)))) -> False.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term26 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2))).
Definition term49 (x0 : Prop) := (~ x0) -> x0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) \/ (x0 x2)) = ((x0 x2) \/ (x1 x2))).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@UNION a0 x0 y0) = (@UNION a0 y0 x0).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) \/ (x0 x2)) /\ ((~ (x0 x2)) /\ (~ (x1 x2)))).
Definition term27 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) \/ (x0 x2)) /\ (~ ((x0 x2) \/ (x1 x2)))) \/ ((~ ((x1 x2) \/ (x0 x2))) /\ ((x0 x2) \/ (x1 x2))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((y0 y1) \/ (x0 y1)).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@UNION a0 x0 y0)) = (@IN a0 y1 (@UNION a0 y0 x0)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) \/ (x0 x2)) /\ (~ ((x0 x2) \/ (x1 x2))).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x1 x2)) /\ (~ (x0 x2))) /\ ((x0 x2) \/ (x1 x2)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term30 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))).
Definition term25 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False.
Definition term28 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x0 y0) \/ (x1 y0)).
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@UNION a0 y0 y1) = (@UNION a0 y1 y0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@UNION a0 x0 y0) = (@UNION a0 y0 x0).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) \/ (x0 x2)) /\ ((~ (x0 x2)) /\ (~ (x1 x2)))) \/ (((~ (x1 x2)) /\ (~ (x0 x2))) /\ ((x0 x2) \/ (x1 x2))).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) \/ (x1 x2)).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (x1 x2).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x0 x2)) /\ (~ (x1 x2))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) \/ (x1 x2)).
Definition term22 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)).
Definition term7 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@UNION a0 y0 y1)) = (@IN a0 y2 (@UNION a0 y1 y0)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 x1 x0)) = (@IN a0 y0 (@UNION a0 x0 x1)).
Definition term29 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y1 y2) \/ (y0 y2)))) -> False.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 x1 x0)) = (@IN a0 y0 (@UNION a0 x0 x1)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((y0 y1) \/ (x0 y1)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@UNION a0 x0 y0)) = (@IN a0 y1 (@UNION a0 y0 x0)).
Definition term6 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@UNION a0 y0 y1) = (@UNION a0 y1 y0).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) \/ (x0 x2))) /\ ((x0 x2) \/ (x1 x2)).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
