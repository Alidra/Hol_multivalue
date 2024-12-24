Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, (@EXTENSIONAL a0 a1 y0) = (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = (@ARB a1)) y2)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = (@ARB a1)) y2)) x0.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => @GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = (@ARB a1)) y2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> a1) (fun y0 : a0 -> a1 => exists y1 : a0 -> a1, @SETSPEC (a0 -> a1) y0 (forall y2 : a0, (~ (@IN a0 y2 x0)) -> (y1 y2) = (@ARB a1)) y1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@EXTENSIONAL a0 a1 y0) = (@GSPEC (a0 -> a1) (fun y1 : a0 -> a1 => exists y2 : a0 -> a1, @SETSPEC (a0 -> a1) y1 (forall y3 : a0, (~ (@IN a0 y3 y0)) -> (y2 y3) = (@ARB a1)) y2))) x0.
