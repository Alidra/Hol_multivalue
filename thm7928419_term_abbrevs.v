Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) := forall y0 : type6 a0, x0 (x1 y0).
Definition term0 (a0 : Type') (x0 : type39 a0) := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x0 y3)) -> y1 y2) -> y1 y0.
