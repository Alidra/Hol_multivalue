Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3) y1) = (y0 y1)) /\ (forall y0 : a1 -> Prop, forall y1 : a1, (@IN a1 y1 (fun y2 : a1 => y0 y2)) = (y0 y1)).
