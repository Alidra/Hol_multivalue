Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : type919 a0, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => y0 (@SETSPEC a0 y2)))) = (y0 (fun y2 : Prop => fun y3 : a0 => y2 /\ (y1 = y3))).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (a4 : Type') := (forall y0 : type919 a0, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => y0 (@SETSPEC a0 y2)))) = (y0 (fun y2 : Prop => fun y3 : a0 => y2 /\ (y1 = y3)))) /\ ((forall y0 : a1 -> Prop, forall y1 : a1, (@IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (y0 y3) y3))) = (y0 y1)) /\ ((forall y0 : type919 a2, forall y1 : a2, (@GSPEC a2 (fun y2 : a2 => y0 (@SETSPEC a2 y2)) y1) = (y0 (fun y2 : Prop => fun y3 : a2 => y2 /\ (y1 = y3)))) /\ ((forall y0 : a3 -> Prop, forall y1 : a3, (@GSPEC a3 (fun y2 : a3 => exists y3 : a3, @SETSPEC a3 y2 (y0 y3) y3) y1) = (y0 y1)) /\ (forall y0 : a4 -> Prop, forall y1 : a4, (@IN a4 y1 (fun y2 : a4 => y0 y2)) = (y0 y1))))).
