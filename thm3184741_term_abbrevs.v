Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) /\ ((forall y0 : type919 a1, forall y1 : a1, (@GSPEC a1 (fun y2 : a1 => y0 (@SETSPEC a1 y2)) y1) = (y0 (fun y2 : Prop => fun y3 : a1 => y2 /\ (y1 = y3)))) /\ ((forall y0 : a2 -> Prop, forall y1 : a2, (@GSPEC a2 (fun y2 : a2 => exists y3 : a2, @SETSPEC a2 y2 (y0 y3) y3) y1) = (y0 y1)) /\ (forall y0 : a3 -> Prop, forall y1 : a3, (@IN a3 y1 (fun y2 : a3 => y0 y2)) = (y0 y1)))).
