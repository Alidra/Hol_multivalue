Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => ((@RESTRICTION a0 a1 x0 y0) = y0) = (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0))) x1.
Definition term13 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : a0 -> a1, x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @IN (a0 -> a1) x0 (@EXTENSIONAL a0 a1 x1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => @IN (a0 -> a1) (@RESTRICTION a0 a1 x0 y0) (@EXTENSIONAL a0 a1 x0)) x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, @IN (a0 -> a1) (@RESTRICTION a0 a1 x0 y0) (@EXTENSIONAL a0 a1 x0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, ((@RESTRICTION a0 a1 x0 y0) = y0) = (@IN (a0 -> a1) y0 (@EXTENSIONAL a0 a1 x0)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => (@RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 x0 y0)) = (@RESTRICTION a0 a1 x0 y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, ((@RESTRICTION a0 a1 y0 y1) = y1) = (@IN (a0 -> a1) y1 (@EXTENSIONAL a0 a1 y0))) x0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, @IN (a0 -> a1) (@RESTRICTION a0 a1 y0 y1) (@EXTENSIONAL a0 a1 y0)) x0.
Definition term10 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => True.
Definition term16 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (@RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 x0 y0)) = (@RESTRICTION a0 a1 x0 y0).
Definition term17 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@RESTRICTION a0 a1 y0 (@RESTRICTION a0 a1 y0 y1)) = (@RESTRICTION a0 a1 y0 y1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @IN (a0 -> a1) (@RESTRICTION a0 a1 x1 x0) (@EXTENSIONAL a0 a1 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := @RESTRICTION a0 a1 x0 (@RESTRICTION a0 a1 x0 x1).
Definition term15 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (@RESTRICTION a0 a1 y0 (@RESTRICTION a0 a1 y0 y1)) = (@RESTRICTION a0 a1 y0 y1).
Definition term18 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term12 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, True.
