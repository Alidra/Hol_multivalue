Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1333 a0 a1) (x1 : type1431 a0 a1) := forall y0 : a0, x0 (x1 y0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1333 a0 a1) (x1 : type1431 a0 a1) (x2 : a0) := (fun y0 : a0 => x0 (x1 y0)) x2.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1333 a0 a1) (x1 : type1431 a0 a1) (x2 : a0) := x0 (x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) (x1 : type1479 a0 a1) := fun y0 : type1677 a0 a1 => forall y1 : type1333 a0 a1, (forall y2 : type1677 a0 a1, ((exists y3 : a0, y2 = (x0 y3)) \/ (exists y3 : a1, y2 = (x1 y3))) -> y1 y2) -> y1 y0.
