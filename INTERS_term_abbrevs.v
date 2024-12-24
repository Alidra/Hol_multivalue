Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') := forall y0 : type686 a0, (@INTERS a0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) -> @IN a0 y2 y3) y2)).
Definition term0 (a0 : Type') := fun y0 : type686 a0 => @GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) -> @IN a0 y2 y3) y2).
Definition term4 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@INTERS a0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) -> @IN a0 y2 y3) y2))) x0.
Definition term2 (a0 : Type') (x0 : type686 a0) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) -> @IN a0 y1 y2) y1).
Definition term1 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => @GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a0 -> Prop, (@IN (a0 -> Prop) y3 y0) -> @IN a0 y2 y3) y2)) x0.
