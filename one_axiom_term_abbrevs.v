Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') := forall y0 : a0 -> unit, forall y1 : a0 -> unit, y0 = y1.
Definition term7 (a0 : Type') (x0 : a0 -> unit) := forall y0 : a0 -> unit, x0 = y0.
Definition term0 (x0 : unit) := (fun y0 : unit => y0 = tt) x0.
Definition term6 (a0 : Type') (x0 : a0 -> unit) (x1 : a0) := @eq unit (x0 x1).
Definition term5 (a0 : Type') (x0 : a0 -> unit) (x1 : a0 -> unit) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
