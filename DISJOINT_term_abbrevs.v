Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@INTER a0 y0 y1) = (@EMPTY a0)) x0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0))) x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0)).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INTER a0 x0 y0) = (@EMPTY a0)) x1.
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@INTER a0 y0 y1) = (@EMPTY a0).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = ((@INTER a0 y0 y1) = (@EMPTY a0))) x0.
Definition term5 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = ((@INTER a0 y0 y1) = (@EMPTY a0)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@INTER a0 x0 y0) = (@EMPTY a0).
