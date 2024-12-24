Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := or (x0 = (@EMPTY a0)).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term8 (a0 : Type') (a1 : Type') := fun y0 : a1 -> Prop => (@CROSS a0 a1 y0 (@EMPTY a0)) = (@EMPTY (prod a1 a0)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, ((@CROSS a1 a0 x0 y0) = (@EMPTY (prod a0 a1))) = ((x0 = (@EMPTY a0)) \/ (y0 = (@EMPTY a1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (x0 = (@EMPTY a0)) \/ True.
Definition term13 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term19 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, (@CROSS a1 a0 (@EMPTY a0) y0) = (@EMPTY (prod a0 a1)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (x0 = (@EMPTY a1)) \/ ((@EMPTY a0) = (@EMPTY a0)).
Definition term14 (a0 : Type') (a1 : Type') := and (forall y0 : a1 -> Prop, (@CROSS a0 a1 y0 (@EMPTY a0)) = (@EMPTY (prod a1 a0))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => ((@CROSS a1 a0 x0 y0) = (@EMPTY (prod a0 a1))) = ((x0 = (@EMPTY a0)) \/ (y0 = (@EMPTY a1)))) x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, ((@CROSS a1 a0 y0 y1) = (@EMPTY (prod a0 a1))) = ((y0 = (@EMPTY a0)) \/ (y1 = (@EMPTY a1)))) x0.
Definition term10 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, (@CROSS a0 a1 y0 (@EMPTY a0)) = (@EMPTY (prod a1 a0)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := True \/ (x0 = (@EMPTY a0)).
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term16 (a0 : Type') := or ((@EMPTY a0) = (@EMPTY a0)).
Definition term18 (a0 : Type') (a1 : Type') := fun y0 : a1 -> Prop => (@CROSS a1 a0 (@EMPTY a0) y0) = (@EMPTY (prod a0 a1)).
Definition term20 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := (forall y0 : a2 -> Prop, (@CROSS a0 a2 y0 (@EMPTY a0)) = (@EMPTY (prod a2 a0))) /\ (forall y0 : a3 -> Prop, (@CROSS a3 a1 (@EMPTY a1) y0) = (@EMPTY (prod a1 a3))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (x0 = (@EMPTY a1)) \/ (x1 = (@EMPTY a0)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (x0 = (@EMPTY a0)) \/ (x1 = (@EMPTY a1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := ((@EMPTY a0) = (@EMPTY a0)) \/ (x0 = (@EMPTY a1)).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, True.
