Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term4 (x0 : Prop) := ~ (~ x0).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, x0 y0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := (~ (exists y0 : a0, x0 y0)) -> False.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> (x0 x1) = False.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := ((~ (exists y0 : a0, x0 y0)) -> forall y0 : a0, ~ (x0 y0)) /\ ((forall y0 : a0, ~ (x0 y0)) -> ~ (exists y0 : a0, x0 y0)).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, x0 y0) -> False.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (exists y0 : a0, x0 y0)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, ~ (x0 y0)) -> ~ (exists y0 : a0, x0 y0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (~ (exists y0 : a0, x0 y0)) -> forall y0 : a0, ~ (x0 y0).
