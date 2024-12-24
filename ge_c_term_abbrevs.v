Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, (@ge_c a0 a1 x0 y0) = (@le_c a1 a0 y0 x0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := fun y0 : a0 -> Prop => @le_c a1 a0 y0 x0.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a1 -> Prop => fun y1 : a0 -> Prop => @le_c a1 a0 y1 y0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, (@ge_c a0 a1 y0 x0) = (@le_c a1 a0 x0 y0).
Definition term9 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (@ge_c a0 a1 y1 y0) = (@le_c a1 a0 y0 y1).
Definition term5 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, (@ge_c a0 a1 y0 y1) = (@le_c a1 a0 y1 y0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => fun y1 : a0 -> Prop => @le_c a1 a0 y1 y0) x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@ge_c a0 a1 x0 y0) = (@le_c a1 a0 y0 x0)) x1.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, (@ge_c a0 a1 y0 y1) = (@le_c a1 a0 y1 y0)) x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @le_c a1 a0 y0 x0) x1.
