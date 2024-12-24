Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@CARD a0 y0) = (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0))) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)) x0.
Definition term3 (a0 : Type') := forall y0 : a0 -> Prop, (@CARD a0 y0) = (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x0 (NUMERAL 0).
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => @ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0).
