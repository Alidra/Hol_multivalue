Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : recspace a0) (x1 : type1338 a0) (x2 : type1432 a0) := (x1 x0) /\ (forall y0 : a0, x1 (x2 y0)).
Definition term0 (a0 : Type') (x0 : recspace a0) (x1 : type1432 a0) := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, y2 = (x1 y3))) -> y1 y2) -> y1 y0.
