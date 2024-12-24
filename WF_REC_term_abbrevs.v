Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := (@WF a0 x0) -> forall y0 : type549 a0 a1, (forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0, (forall y4 : a0, (x0 y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> exists y1 : a0 -> a1, forall y2 : a0, (y1 y2) = (y0 y1 y2).
