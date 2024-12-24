Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => fun y1 : a0 => fun y2 : a0 => Peano.lt (y0 y1) (y0 y2)) x0.
Definition term0 (a0 : Type') := fun y0 : a0 -> nat => fun y1 : a0 => fun y2 : a0 => Peano.lt (y0 y1) (y0 y2).
Definition term2 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1).
Definition term4 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => (@MEASURE a0 y0) = (fun y1 : a0 => fun y2 : a0 => Peano.lt (y0 y1) (y0 y2))) x0.
Definition term3 (a0 : Type') := forall y0 : a0 -> nat, (@MEASURE a0 y0) = (fun y1 : a0 => fun y2 : a0 => Peano.lt (y0 y1) (y0 y2)).
