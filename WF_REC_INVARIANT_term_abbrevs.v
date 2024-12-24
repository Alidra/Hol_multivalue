Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := (@WF a0 x0) -> forall y0 : type549 a0 a1, forall y1 : type1413 a0 a1, (forall y2 : a0 -> a1, forall y3 : a0 -> a1, forall y4 : a0, (forall y5 : a0, (x0 y5 y4) -> ((y2 y5) = (y3 y5)) /\ (y1 y5 (y2 y5))) -> ((y0 y2 y4) = (y0 y3 y4)) /\ (y1 y4 (y0 y2 y4))) -> exists y2 : a0 -> a1, forall y3 : a0, (y2 y3) = (y0 y2 y3).
