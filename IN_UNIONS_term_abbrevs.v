Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term12 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term11 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@IN a0 y0 y1).
Definition term31 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => (@IN a0 y0 (@UNIONS a0 x0)) = (exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@IN a0 y0 y1)).
Definition term35 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term19 (a0 : Type') (x0 : a0) (x1 : type686 a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) /\ (@IN a0 y1 y2)) y0) y0.
Definition term7 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@UNIONS a0 x1).
Definition term34 (a0 : Type') := forall y0 : a0, True.
Definition term22 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ (@IN a0 y1 y2)) y1.
Definition term36 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0, (@IN a0 y1 (@UNIONS a0 y0)) = (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@IN a0 y1 y2)).
Definition term21 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x0) /\ (@IN a0 y2 y3)) y1) y1.
Definition term38 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0, (@IN a0 y1 (@UNIONS a0 y0)) = (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@IN a0 y1 y2)).
Definition term30 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop (((exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0)) = (exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0))) = True).
Definition term9 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x1) /\ (@IN a0 y2 y3)) y1) y1)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) /\ (@IN a0 y1 y2)) y1)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : type686 a0) := exists y0 : a0, @SETSPEC a0 x0 (exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) /\ (@IN a0 y0 y1)) y0.
Definition term25 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) /\ (@IN a0 y1 y2)) y1))).
Definition term24 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x1) /\ (@IN a0 y2 y3)) y1) y1))).
Definition term16 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0) := @SETSPEC a0 x0 (exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) /\ (@IN a0 x2 y0)) x2.
Definition term0 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@UNIONS a0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (exists y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) /\ (@IN a0 y2 y3)) y2))) x0.
Definition term26 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @eq Prop (@IN a0 x0 (@UNIONS a0 x1)).
Definition term23 (a0 : Type') (x0 : type686 a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => exists y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 x0) /\ (@IN a0 y2 y3)) y1) y1).
Definition term1 (a0 : Type') (x0 : type686 a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ (@IN a0 y1 y2)) y1).
Definition term39 (a0 : Type') := forall y0 : type686 a0, True.
Definition term29 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop ((fun y0 : Prop => y0 = True) ((exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0)) = (exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0)))).
Definition term32 (a0 : Type') := fun y0 : a0 => True.
Definition term17 (a0 : Type') (x0 : a0) (x1 : type686 a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x1) /\ (@IN a0 y1 y2)) y0) y0.
Definition term15 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) /\ (@IN a0 y0 y1)) x2) x2.
Definition term37 (a0 : Type') := fun y0 : type686 a0 => True.
Definition term33 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, (@IN a0 y0 (@UNIONS a0 x0)) = (exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@IN a0 y0 y1)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term10 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (fun y0 : a0 => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@IN a0 y0 y1)) x1.
Definition term14 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0) := @SETSPEC a0 x0 (exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x1) /\ (@IN a0 x2 y0)).
Definition term18 (a0 : Type') (x0 : a0) (x1 : type686 a0) := fun y0 : a0 => @SETSPEC a0 x0 (exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) /\ (@IN a0 y0 y1)) y0.
Definition term40 (a0 : Type') (x0 : Prop) := forall y0 : type686 a0, x0.
Definition term13 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x1) /\ (@IN a0 y0 y1)) x2).
Definition term27 (a0 : Type') (x0 : type686 a0) (x1 : a0) := @eq Prop (exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0)).
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (fun y0 : Prop => y0 = True) ((exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0)) = (exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0))).
Definition term2 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
