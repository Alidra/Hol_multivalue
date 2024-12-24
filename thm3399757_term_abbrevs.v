Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => False) x1) x1.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => False) x1).
Definition term11 (a0 : Type') := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 False y1.
Definition term21 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term8 (a0 : Type') (x0 : a0) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => False) y0) y0.
Definition term20 (a0 : Type') := forall y0 : a0, True.
Definition term19 (a0 : Type') := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 False y2))) = (@IN a0 y0 (@EMPTY a0)).
Definition term10 (a0 : Type') := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => False) y1) y1.
Definition term14 (a0 : Type') (x0 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 False y1)).
Definition term1 (a0 : Type') (x0 : a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => False) y1) y1)).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term17 (a0 : Type') := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 False y2))) = (@IN a0 y0 (@EMPTY a0)).
Definition term16 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 False y1))).
Definition term15 (a0 : Type') (x0 : a0) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => False) y1) y1))).
Definition term9 (a0 : Type') (x0 : a0) := exists y0 : a0, @SETSPEC a0 x0 False y0.
Definition term13 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 False y1).
Definition term12 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => False) y1) y1).
Definition term18 (a0 : Type') := fun y0 : a0 => True.
Definition term2 (a0 : Type') (x0 : a0) := (fun y0 : a0 => False) x0.
Definition term7 (a0 : Type') (x0 : a0) := fun y0 : a0 => @SETSPEC a0 x0 False y0.
Definition term3 (a0 : Type') := fun y0 : a0 => False.
Definition term6 (a0 : Type') (x0 : a0) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => False) y0) y0.
