Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := @eq Prop (@IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((@IN a1 y1 x1) /\ (~ ((x2 y1) = (@neutral a0 x3)))) y1))).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := @eq Prop (@IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => (@IN a1 y2 x1) /\ (~ ((x2 y2) = (@neutral a0 x3)))) y1) y1))).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) (x4 : a1) := @SETSPEC a1 x0 ((fun y0 : a1 => (@IN a1 y0 x1) /\ (~ ((x2 y0) = (@neutral a0 x3)))) x4).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3))) x1.
Definition term17 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := (@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3))).
Definition term37 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : type1400 a0) := fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => (@IN a1 y2 x0) /\ (~ ((x1 y2) = (@neutral a0 x2)))) y1) y1.
Definition term50 (a0 : Type') (a1 : Type') := forall y0 : type1400 a0, forall y1 : a1 -> a0, forall y2 : a1, forall y3 : a1 -> Prop, (@IN a1 y2 (@support a1 a0 y0 y1 y3)) = ((@IN a1 y2 y3) /\ (~ ((y1 y2) = (@neutral a0 y0)))).
Definition term42 (a0 : Type') := forall y0 : a0, True.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : type1400 a1, (@support a0 a1 y2 y1 y0) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4))) x0.
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : type1400 a0, x0.
Definition term47 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a1 -> a0, x0.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term25 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := exists y0 : a1, @SETSPEC a1 x0 ((@IN a1 y0 x1) /\ (~ ((x2 y0) = (@neutral a0 x3)))) y0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := @IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => (@IN a1 y2 x1) /\ (~ ((x2 y2) = (@neutral a0 x3)))) y1) y1)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := @IN a1 x0 (@GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((@IN a1 y1 x1) /\ (~ ((x2 y1) = (@neutral a0 x3)))) y1)).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : type1400 a0) := @GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((fun y2 : a1 => (@IN a1 y2 x0) /\ (~ ((x1 y2) = (@neutral a0 x2)))) y1) y1).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : type1400 a0) := @GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((@IN a1 y1 x0) /\ (~ ((x1 y1) = (@neutral a0 x2)))) y1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (fun y0 : type1400 a1 => (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2))) x2.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term48 (a0 : Type') (a1 : Type') := fun y0 : type1400 a0 => forall y1 : a1 -> a0, forall y2 : a1, forall y3 : a1 -> Prop, (@IN a1 y2 (@support a1 a0 y0 y1 y3)) = ((@IN a1 y2 y3) /\ (~ ((y1 y2) = (@neutral a0 y0)))).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : type1400 a0) (x3 : a1) := (fun y0 : a1 => (@IN a1 y0 x0) /\ (~ ((x1 y0) = (@neutral a0 x2)))) x3.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : type1400 a0) := fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 ((@IN a1 y1 x0) /\ (~ ((x1 y1) = (@neutral a0 x2)))) y1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1400 a0) (x2 : a1 -> a0) (x3 : a1 -> Prop) := @eq Prop (@IN a1 x0 (@support a1 a0 x1 x2 x3)).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral a1 x2)))) y1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := fun y0 : a1 => @SETSPEC a1 x0 ((fun y1 : a1 => (@IN a1 y1 x1) /\ (~ ((x2 y1) = (@neutral a0 x3)))) y0) y0.
Definition term40 (a0 : Type') := fun y0 : a0 => True.
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) := forall y0 : a1, forall y1 : a1 -> Prop, (@IN a1 y0 (@support a1 a0 x1 x0 y1)) = ((@IN a1 y0 y1) /\ (~ ((x0 y0) = (@neutral a0 x1)))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1400 a0) (x2 : a1 -> a0) (x3 : a1 -> Prop) := @IN a1 x0 (@support a1 a0 x1 x2 x3).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) (x4 : a1) := @SETSPEC a1 x0 ((fun y0 : a1 => (@IN a1 y0 x1) /\ (~ ((x2 y0) = (@neutral a0 x3)))) x4) x4.
Definition term49 (a0 : Type') := fun y0 : type1400 a0 => True.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := @eq Prop ((@IN a1 x2 x0) /\ (~ ((x1 x2) = (@neutral a0 x3)))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) := forall y0 : a1 -> Prop, (@IN a1 x1 (@support a1 a0 x2 x0 y0)) = ((@IN a1 x1 y0) /\ (~ ((x0 x1) = (@neutral a0 x2)))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : type1400 a0) := fun y0 : a1 => (@IN a1 y0 x0) /\ (~ ((x1 y0) = (@neutral a0 x2))).
Definition term34 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : a1) (x4 : type1400 a0) := @SETSPEC a1 x0 ((@IN a1 x3 x1) /\ (~ ((x2 x3) = (@neutral a0 x4)))).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : type1400 a1, (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) := fun y0 : a1 -> Prop => (@IN a1 x1 (@support a1 a0 x2 x0 y0)) = ((@IN a1 x1 y0) /\ (~ ((x0 x1) = (@neutral a0 x2)))).
Definition term44 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => True.
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := forall y0 : a1 -> a0, forall y1 : a1, forall y2 : a1 -> Prop, (@IN a1 y1 (@support a1 a0 x0 y0 y2)) = ((@IN a1 y1 y2) /\ (~ ((y0 y1) = (@neutral a0 x0)))).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := fun y0 : a1 -> a0 => forall y1 : a1, forall y2 : a1 -> Prop, (@IN a1 y1 (@support a1 a0 x0 y0 y2)) = ((@IN a1 y1 y2) /\ (~ ((y0 y1) = (@neutral a0 x0)))).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) := fun y0 : a1 => forall y1 : a1 -> Prop, (@IN a1 y0 (@support a1 a0 x1 x0 y1)) = ((@IN a1 y0 y1) /\ (~ ((x0 y0) = (@neutral a0 x1)))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := fun y0 : a1 => @SETSPEC a1 x0 ((@IN a1 y0 x1) /\ (~ ((x2 y0) = (@neutral a0 x3)))) y0.
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) (x4 : a1) := @SETSPEC a1 x0 ((@IN a1 x4 x1) /\ (~ ((x2 x4) = (@neutral a0 x3)))) x4.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a1 -> Prop) (x2 : a1 -> a0) (x3 : type1400 a0) := exists y0 : a1, @SETSPEC a1 x0 ((fun y1 : a1 => (@IN a1 y1 x1) /\ (~ ((x2 y1) = (@neutral a0 x3)))) y0) y0.
Definition term51 (a0 : Type') := forall y0 : type1400 a0, True.
Definition term46 (a0 : Type') (a1 : Type') := forall y0 : a1 -> a0, True.
Definition term36 (a0 : Type') := forall y0 : a0 -> Prop, True.
