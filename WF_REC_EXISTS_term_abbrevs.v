Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := (@WF a0 x0) -> forall y0 : type547 a0 a1, ((forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0, forall y4 : a1, (forall y5 : a0, (x0 y5 y3) -> (y1 y5) = (y2 y5)) -> (y0 y1 y3 y4) = (y0 y2 y3 y4)) /\ (forall y1 : a0 -> a1, forall y2 : a0, (forall y3 : a0, (x0 y3 y2) -> y0 y1 y3 (y1 y3)) -> exists y3 : a1, y0 y1 y2 y3)) -> exists y1 : a0 -> a1, forall y2 : a0, y0 y1 y2 (y1 y2).
