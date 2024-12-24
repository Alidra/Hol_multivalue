Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := (@ex1 a0 x0) -> ex x0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (ex y0) /\ (forall y1 : a0, forall y2 : a0, ((y0 y1) /\ (y0 y2)) -> y1 = y2)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) /\ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := (@ex1 a0 x0) -> (ex x0) /\ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := ((@ex1 a0 x0) = ((ex x0) /\ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1))) -> (@ex1 a0 x0) -> (ex x0) /\ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (@ex1 a0 x0).
