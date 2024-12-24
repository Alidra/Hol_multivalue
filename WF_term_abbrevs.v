Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : type1402 a0 => forall y1 : a0 -> Prop, (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (y0 y3 y2) -> ~ (y1 y3)).
Definition term4 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => (@WF a0 y0) = (forall y1 : a0 -> Prop, (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (y0 y3 y2) -> ~ (y1 y3)))) x0.
Definition term1 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : a0 -> Prop, (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (y0 y3 y2) -> ~ (y1 y3))) x0.
Definition term3 (a0 : Type') := forall y0 : type1402 a0, (@WF a0 y0) = (forall y1 : a0 -> Prop, (exists y2 : a0, y1 y2) -> exists y2 : a0, (y1 y2) /\ (forall y3 : a0, (y0 y3 y2) -> ~ (y1 y3))).
Definition term2 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (exists y1 : a0, y0 y1) -> exists y1 : a0, (y0 y1) /\ (forall y2 : a0, (x0 y2 y1) -> ~ (y0 y2)).
