Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : Prop) := fun y0 : a0 => x0.
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : Prop, (exists y1 : a0, x0 /\ y0) = ((exists y1 : a0, x0) /\ (exists y1 : a0, y0)).
Definition term7 (a0 : Type') (x0 : Prop) (x1 : Prop) := ((exists y0 : a0, x0 /\ x1) -> (exists y0 : a0, x0) /\ (exists y0 : a0, x1)) /\ (((exists y0 : a0, x0) /\ (exists y0 : a0, x1)) -> exists y0 : a0, x0 /\ x1).
Definition term6 (a0 : Type') (x0 : Prop) (x1 : Prop) := ((exists y0 : a0, x0) /\ (exists y0 : a0, x1)) -> exists y0 : a0, x0 /\ x1.
Definition term9 (a0 : Type') := forall y0 : Prop, forall y1 : Prop, (exists y2 : a0, y0 /\ y1) = ((exists y2 : a0, y0) /\ (exists y2 : a0, y1)).
Definition term0 (a0 : Type') (x0 : Prop) (x1 : Prop) := exists y0 : a0, x0 /\ x1.
Definition term1 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term5 (a0 : Type') (x0 : Prop) (x1 : Prop) := (exists y0 : a0, x0 /\ x1) -> (exists y0 : a0, x0) /\ (exists y0 : a0, x1).
Definition term4 (a0 : Type') (x0 : Prop) (x1 : Prop) := (exists y0 : a0, x0) /\ (exists y0 : a0, x1).
Definition term3 (a0 : Type') (x0 : Prop) (x1 : Prop) := fun y0 : a0 => x0 /\ x1.
