Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (a0 : Type') := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 True y2))) = (@IN a0 y0 (@UNIV a0)).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => True) x1).
Definition term20 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term8 (a0 : Type') (x0 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => True) y0) y0.
Definition term19 (a0 : Type') := forall y0 : a0, True.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => True) x1) x1.
Definition term10 (a0 : Type') := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => True) y1) y1.
Definition term14 (a0 : Type') (x0 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1)).
Definition term1 (a0 : Type') (x0 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => True) y1) y1)).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term16 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1))).
Definition term15 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => True) y1) y1))).
Definition term13 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1).
Definition term12 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => True) y1) y1).
Definition term3 (a0 : Type') := fun y0 : a0 => True.
Definition term11 (a0 : Type') := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1.
Definition term6 (a0 : Type') (x0 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => True) y0) y0.
Definition term2 (a0 : Type') (x0 : a0) := (fun y0 : a0 => True) x0.
Definition term7 (a0 : Type') (x0 : a0) := fun y0 : a0 => @SETSPEC a0 x0 True y0.
Definition term9 (a0 : Type') (x0 : a0) := exists y0 : a0, @SETSPEC a0 x0 True y0.
Definition term18 (a0 : Type') := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 True y2))) = (@IN a0 y0 (@UNIV a0)).
