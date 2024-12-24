Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (@RESTRICTION a0 a1 x0 y0) = (fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1))) x1.
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 => (fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (x1 y1) (@ARB a1)) y0.
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 ((fun y0 : a0 => (fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (x1 y1) (@ARB a1)) y0) x2).
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1))) x2.
Definition term22 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : a0, (@RESTRICTION a0 a1 y0 y1 y2) = (@COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1))) x0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a1 x0 x1 y0) = ((fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (x1 y1) (@ARB a1)) y0).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term28 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term31 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@RESTRICTION a0 a1 y0 y1) = (fun y2 : a0 => @COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1)).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 => (@RESTRICTION a0 a1 x0 x1 y0) = ((fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (x1 y1) (@ARB a1)) y0).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (x1 y1) (@ARB a1)) y0) x2.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 ((fun y0 : a0 => @COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1)) x2).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term21 (a0 : Type') := fun y0 : a0 => True.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 (@RESTRICTION a0 a1 x0 x1 x2).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := (fun y0 : a0 => @COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1)) x2.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : a0 => @COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1).
Definition term25 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term30 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a0) := @eq a1 (@COND a1 (@IN a0 x2 x0) (x1 x2) (@ARB a1)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => (@RESTRICTION a0 a1 x0 y0) = (fun y1 : a0 => @COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)).
Definition term29 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@RESTRICTION a0 a1 y0 y1) = (fun y2 : a0 => @COND a1 (@IN a0 y2 y0) (y1 y2) (@ARB a1)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : a0, (@RESTRICTION a0 a1 x0 y0 y1) = (@COND a1 (@IN a0 y1 x0) (y0 y1) (@ARB a1)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term32 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term27 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, (@RESTRICTION a0 a1 x0 x1 y0) = (@COND a1 (@IN a0 y0 x0) (x1 y0) (@ARB a1)).
