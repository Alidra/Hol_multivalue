Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a1, exists y2 : a0, y1 = (y0 y2)) x0.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a1, exists y2 : a0, y1 = (y0 y2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (@ONTO a0 a1 y0) = (forall y1 : a1, exists y2 : a0, y1 = (y0 y2))) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a1, exists y1 : a0, y0 = (x0 y1).
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (@ONTO a0 a1 y0) = (forall y1 : a1, exists y2 : a0, y1 = (y0 y2)).
