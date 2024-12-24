Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type549 a0 a1) (x1 : type1402 a0) (x2 : type1413 a0 a1) := (forall y0 : a0 -> a1, forall y1 : a0, (forall y2 : a0, (x1 y2 y1) -> x2 y2 (y0 y2)) -> x2 y1 (x0 y0 y1)) /\ ((forall y0 : type1413 a0 a1, (forall y1 : a0 -> a1, forall y2 : a0, (forall y3 : a0, (x1 y3 y2) -> y0 y3 (y1 y3)) -> y0 y2 (x0 y1 y2)) -> forall y1 : a0, forall y2 : a1, (x2 y1 y2) -> y0 y1 y2) /\ (forall y0 : a0, forall y1 : a1, (x2 y0 y1) = (exists y2 : a0 -> a1, (y1 = (x0 y2 y0)) /\ (forall y3 : a0, (x1 y3 y0) -> x2 y3 (y2 y3))))).
