Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => fun y1 : a0 => y0 y1.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, (@LET a0 a1 x0 y0) = (x0 y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => fun y1 : a0 => y0 y1) x0.
Definition term5 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0, (@LET a0 a1 y0 y1) = (y0 y1).
