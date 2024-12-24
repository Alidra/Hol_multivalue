Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := (forall y0 : type919 a0, forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => y0 (@SETSPEC a0 y2)) y1) = (y0 (fun y2 : Prop => fun y3 : a0 => y2 /\ (y1 = y3)))) /\ ((forall y0 : a1 -> Prop, forall y1 : a1, (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (y0 y3) y3) y1) = (y0 y1)) /\ (forall y0 : a2 -> Prop, forall y1 : a2, (@IN a2 y1 (fun y2 : a2 => y0 y2)) = (y0 y1))).
