Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) := (fun y0 : a0 => (x0 y0) -> x1) x2.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, x0 y0.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, (x0 y0) -> x1) -> (exists y0 : a0, x0 y0) -> x1.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((forall y0 : a0, (x0 y0) -> x1) -> (exists y0 : a0, x0 y0) -> x1) /\ (((exists y0 : a0, x0 y0) -> x1) -> forall y0 : a0, (x0 y0) -> x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (x0 x1) -> x2.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := ((exists y0 : a0, x0 y0) -> x1) -> forall y0 : a0, (x0 y0) -> x1.