Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) \/ (y0 = x1)) x2.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INSERT a0 x1 x2)).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) \/ (x1 = x2).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) \/ (y0 = x2)) x3).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 x0) \/ (y0 = x1).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) \/ (y1 = x2)) y0) y0.
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term17 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((@IN a0 x0 y1) \/ (x0 = y0)).
Definition term16 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term48 (a0 : Type') := forall y0 : a0, True.
Definition term46 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term5 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 \/ y1) = (y1 \/ y0)) x0.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) \/ (y2 = x1)) y1) y1.
Definition term21 (a0 : Type') := fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((@IN a0 y0 y2) \/ (y0 = y1)).
Definition term20 (a0 : Type') := fun y0 : a0 => forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2)).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) \/ (y2 = x2)) y1) y1)).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) \/ (y1 = x2)) y1)).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN a0 x0 (@INSERT a0 x1 y0)) = ((@IN a0 x0 y0) \/ (x0 = x1)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) \/ (y1 = x2)) y1))).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) \/ (y2 = x2)) y1) y1))).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := @eq Prop ((@IN a0 x1 x0) \/ (x1 = x2)).
Definition term7 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 \/ y0) = (y0 \/ x0)) x1.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) \/ (y2 = x1)) y1) y1).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) \/ (y1 = x1)) y1).
Definition term47 (a0 : Type') := fun y0 : a0 => True.
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) \/ (y1 = x2)) y0) y0.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) \/ (y0 = x2)) y0.
Definition term23 (a0 : Type') := forall y0 : a0, forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((@IN a0 y0 y2) \/ (y0 = y1)).
Definition term22 (a0 : Type') := forall y0 : a0, forall y1 : a0, forall y2 : a0 -> Prop, (@IN a0 y0 (@INSERT a0 y1 y2)) = ((y0 = y1) \/ (@IN a0 y0 y2)).
Definition term43 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) \/ (x3 = x2)) x3.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) \/ (y1 = x1)) y1.
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) \/ (y0 = x2)) y0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x2 x1) \/ (x2 = x3)).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) \/ (y0 = x2)) x3) x3.
Definition term6 (x0 : Prop) := forall y0 : Prop, (x0 \/ y0) = (y0 \/ x0).
Definition term19 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((@IN a0 x0 y1) \/ (x0 = y0)).
Definition term18 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 y0 y1)) = ((x0 = y0) \/ (@IN a0 x0 y1)).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x0 (@INSERT a0 x1 y0)) = ((@IN a0 x0 y0) \/ (x0 = x1)).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN a0 x1 (@INSERT a0 x0 y0)) = ((x1 = x0) \/ (@IN a0 x1 y0)).
Definition term44 (a0 : Type') := forall y0 : a0 -> Prop, True.
