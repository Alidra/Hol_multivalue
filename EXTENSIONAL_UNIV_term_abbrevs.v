Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := exists y0 : a1 -> a0, @SETSPEC (a1 -> a0) x0 (forall y1 : a1, (~ (@IN a1 y1 (@UNIV a1))) -> (y0 y1) = (@ARB a0)) y0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3) y1) = (y0 y1)) x0.
Definition term18 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : a1 -> a0 => @SETSPEC (a1 -> a0) x0 True y0.
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : a1 -> a0 => @SETSPEC (a1 -> a0) x0 ((fun y1 : a1 -> a0 => True) y0) y0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : a1, (~ (@IN a1 y0 (@UNIV a1))) -> (x0 y0) = (@ARB a0).
Definition term17 (a0 : Type') := forall y0 : a0, True.
Definition term44 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a1 -> a0, x0.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := (fun y0 : a1 -> a0 => True) x0.
Definition term41 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => @EXTENSIONAL a1 a0 (@UNIV a1) y0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := False -> (x0 x1) = (@ARB a0).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := exists y0 : a1 -> a0, @SETSPEC (a1 -> a0) x0 ((fun y1 : a1 -> a0 => True) y0) y0.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := exists y0 : a1 -> a0, @SETSPEC (a1 -> a0) x0 True y0.
Definition term5 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term15 (a0 : Type') := fun y0 : a0 => True.
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := @eq Prop (@GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 True y1) x0).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := @eq Prop (@GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 ((fun y2 : a1 -> a0 => True) y1) y1) x0).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : a1 => (~ (@IN a1 y0 (@UNIV a1))) -> (x0 y0) = (@ARB a0).
Definition term26 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 True y1.
Definition term11 (a0 : Type') (x0 : a0) := imp (~ (@IN a0 x0 (@UNIV a0))).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> a0) := @SETSPEC (a1 -> a0) x0 (forall y0 : a1, (~ (@IN a1 y0 (@UNIV a1))) -> (x1 y0) = (@ARB a0)).
Definition term37 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 ((fun y2 : a1 -> a0 => True) y1) y1.
Definition term25 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 (forall y2 : a1, (~ (@IN a1 y2 (@UNIV a1))) -> (y1 y2) = (@ARB a0)) y1.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> a0) := @SETSPEC (a1 -> a0) x0 (forall y0 : a1, (~ (@IN a1 y0 (@UNIV a1))) -> (x1 y0) = (@ARB a0)) x1.
Definition term38 (a0 : Type') (a1 : Type') := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 ((fun y2 : a1 -> a0 => True) y1) y1).
Definition term27 (a0 : Type') (a1 : Type') := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 True y1).
Definition term9 (a0 : Type') (a1 : Type') := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 (forall y2 : a1, (~ (@IN a1 y2 (@UNIV a1))) -> (y1 y2) = (@ARB a0)) y1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 (forall y2 : a1, (~ (@IN a1 y2 x0)) -> (y1 y2) = (@ARB a0)) y1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> a1) (fun y0 : a0 -> a1 => exists y1 : a0 -> a1, @SETSPEC (a0 -> a1) y0 (forall y2 : a0, (~ (@IN a0 y2 x0)) -> (y1 y2) = (@ARB a1)) y1).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> a0) := @SETSPEC (a1 -> a0) x0 ((fun y0 : a1 -> a0 => True) x1) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@EXTENSIONAL a0 a1 y0) = (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = (@ARB a1)) y2))) x0.
Definition term32 (a0 : Type') (a1 : Type') := fun y0 : a1 -> a0 => True.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2) y0) = (x0 y0)) x1.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2) y0) = (x0 y0).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> a0) := @SETSPEC (a1 -> a0) x0 ((fun y0 : a1 -> a0 => True) x1).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := fun y0 : a1 -> a0 => @SETSPEC (a1 -> a0) x0 (forall y1 : a1, (~ (@IN a1 y1 (@UNIV a1))) -> (y0 y1) = (@ARB a0)) y0.
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 ((fun y2 : a1 -> a0 => True) y1) y1) x0.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 True y1) x0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) := (~ (@IN a1 x1 (@UNIV a1))) -> (x0 x1) = (@ARB a0).
Definition term10 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@UNIV a0)).
Definition term42 (a0 : Type') (a1 : Type') := forall y0 : a1 -> a0, @EXTENSIONAL a1 a0 (@UNIV a1) y0.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x0 y1) y1) x1.
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3) y1) = (y0 y1).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type805 a0 a1) (x1 : a1 -> a0) := @GSPEC (a1 -> a0) (fun y0 : a1 -> a0 => exists y1 : a1 -> a0, @SETSPEC (a1 -> a0) y0 (x0 y1) y1) x1.
Definition term43 (a0 : Type') (a1 : Type') := forall y0 : a1 -> a0, True.
