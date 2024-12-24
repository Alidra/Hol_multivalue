Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := @eq Prop (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 x1) (@CROSS a1 a0 x2 x3)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) (x3 : a1 -> Prop) := @eq Prop (((@INTER a0 x0 x1) = (@EMPTY a0)) \/ ((@INTER a1 x2 x3) = (@EMPTY a1))).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := forall y0 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 x2) (@CROSS a1 a0 x1 y0)) = ((@DISJOINT a0 x0 x1) \/ (@DISJOINT a1 x2 y0)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := forall y0 : a1 -> Prop, (@INTER (prod a0 a1) (@CROSS a1 a0 x0 x2) (@CROSS a1 a0 x1 y0)) = (@CROSS a1 a0 (@INTER a0 x0 x1) (@INTER a1 x2 y0)).
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term36 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, forall y2 : a0 -> Prop, forall y3 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 y0 y1) (@CROSS a1 a0 y2 y3)) = ((@DISJOINT a0 y0 y2) \/ (@DISJOINT a1 y1 y3)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 y0) (@CROSS a1 a0 y1 y2)) = ((@DISJOINT a0 x0 y1) \/ (@DISJOINT a1 y0 y2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, forall y2 : a1 -> Prop, (@INTER (prod a0 a1) (@CROSS a1 a0 x0 y1) (@CROSS a1 a0 y0 y2)) = (@CROSS a1 a0 (@INTER a0 x0 y0) (@INTER a1 y1 y2)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a1 -> Prop, ((@CROSS a1 a0 x0 y0) = (@EMPTY (prod a0 a1))) = ((x0 = (@EMPTY a0)) \/ (y0 = (@EMPTY a1))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, forall y3 : a1 -> Prop, (@INTER (prod a0 a1) (@CROSS a1 a0 y0 y2) (@CROSS a1 a0 y1 y3)) = (@CROSS a1 a0 (@INTER a0 y0 y1) (@INTER a1 y2 y3))) x0.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := @DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 x1) (@CROSS a1 a0 x2 x3).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 y0) (@CROSS a1 a0 y1 y2)) = ((@DISJOINT a0 x0 y1) \/ (@DISJOINT a1 y0 y2)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) (x3 : a1 -> Prop) := @eq ((prod a0 a1) -> Prop) (@CROSS a1 a0 (@INTER a0 x0 x1) (@INTER a1 x2 x3)).
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0))) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 x1) (@CROSS a1 a0 y0 y1)) = ((@DISJOINT a0 x0 y0) \/ (@DISJOINT a1 x1 y1)).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@DISJOINT a0 x0 y0) = ((@INTER a0 x0 y0) = (@EMPTY a0)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := @INTER (prod a0 a1) (@CROSS a1 a0 x0 x1) (@CROSS a1 a0 x2 x3).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a1 -> Prop, (@INTER (prod a0 a1) (@CROSS a1 a0 x0 y0) (@CROSS a1 a0 x1 y1)) = (@CROSS a1 a0 (@INTER a0 x0 x1) (@INTER a1 y0 y1))) x2.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) (x3 : a1 -> Prop) := (@DISJOINT a0 x0 x1) \/ (@DISJOINT a1 x2 x3).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) (x3 : a1 -> Prop) := ((@INTER a0 x0 x1) = (@EMPTY a0)) \/ ((@INTER a1 x2 x3) = (@EMPTY a1)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (@DISJOINT a0 x0 x1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, forall y2 : a1 -> Prop, (@INTER (prod a0 a1) (@CROSS a1 a0 x0 y1) (@CROSS a1 a0 y0 y2)) = (@CROSS a1 a0 (@INTER a0 x0 y0) (@INTER a1 y1 y2))) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (fun y0 : a1 -> Prop => ((@CROSS a1 a0 x0 y0) = (@EMPTY (prod a0 a1))) = ((x0 = (@EMPTY a0)) \/ (y0 = (@EMPTY a1)))) x1.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@DISJOINT a0 y0 y1) = ((@INTER a0 y0 y1) = (@EMPTY a0))) x0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, ((@CROSS a1 a0 y0 y1) = (@EMPTY (prod a0 a1))) = ((y0 = (@EMPTY a0)) \/ (y1 = (@EMPTY a1)))) x0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) (x3 : a1 -> Prop) := @CROSS a1 a0 (@INTER a0 x0 x1) (@INTER a1 x2 x3).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@INTER (prod a0 a1) (@CROSS a1 a0 x0 x2) (@CROSS a1 a0 x1 y0)) = (@CROSS a1 a0 (@INTER a0 x0 x1) (@INTER a1 x2 y0))) x3.
Definition term26 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 x1) (@CROSS a1 a0 y0 y1)) = ((@DISJOINT a0 x0 y0) \/ (@DISJOINT a1 x1 y1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, (@INTER (prod a0 a1) (@CROSS a1 a0 x0 y0) (@CROSS a1 a0 x1 y1)) = (@CROSS a1 a0 (@INTER a0 x0 x1) (@INTER a1 y0 y1)).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((@INTER a0 x0 x1) = (@EMPTY a0)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := @eq ((prod a0 a1) -> Prop) (@INTER (prod a0 a1) (@CROSS a1 a0 x0 x1) (@CROSS a1 a0 x2 x3)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> Prop) := fun y0 : a1 -> Prop => (@DISJOINT (prod a0 a1) (@CROSS a1 a0 x0 x2) (@CROSS a1 a0 x1 y0)) = ((@DISJOINT a0 x0 x1) \/ (@DISJOINT a1 x2 y0)).
Definition term35 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, forall y2 : a0 -> Prop, forall y3 : a1 -> Prop, (@DISJOINT (prod a0 a1) (@CROSS a1 a0 y0 y1) (@CROSS a1 a0 y2 y3)) = ((@DISJOINT a0 y0 y2) \/ (@DISJOINT a1 y1 y3)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := (x0 = (@EMPTY a0)) \/ (x1 = (@EMPTY a1)).
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, True.
