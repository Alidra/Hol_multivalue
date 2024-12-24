Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, ((@cons a0 x0 y1) = (@cons a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2)).
Definition term13 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : list a0, forall y1 : list a0, ((@cons a0 x0 y0) = (@cons a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1)).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : a0, forall y2 : list a0, ((@cons a0 x0 y0) = (@cons a0 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term20 (a0 : Type') := forall y0 : a0, True.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : a0, forall y3 : list a0, ((@cons a0 y0 y1) = (@cons a0 y2 y3)) = ((y0 = y2) /\ (y1 = y3))) x0.
Definition term21 (a0 : Type') := fun y0 : a0 => forall y1 : a0, forall y2 : list a0, forall y3 : list a0, ((@cons a0 y0 y2) = (@cons a0 y1 y3)) = ((y0 = y1) /\ (y2 = y3)).
Definition term12 (a0 : Type') := forall y0 : list a0, True.
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : a0, forall y2 : list a0, ((@cons a0 x0 y0) = (@cons a0 y1 y2)) = ((x0 = y1) /\ (y0 = y2))) x1.
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := @eq Prop ((x0 = x1) /\ (x2 = x3)).
Definition term18 (a0 : Type') := fun y0 : a0 => True.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : list a0 => forall y1 : list a0, ((@cons a0 x0 y0) = (@cons a0 x1 y1)) = ((x0 = x1) /\ (y0 = y1)).
Definition term22 (a0 : Type') := forall y0 : a0, forall y1 : a0, forall y2 : list a0, forall y3 : list a0, ((@cons a0 y0 y2) = (@cons a0 y1 y3)) = ((y0 = y1) /\ (y2 = y3)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (fun y0 : list a0 => ((@cons a0 x0 x2) = (@cons a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term4 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := (fun y0 : a0 => forall y1 : list a0, ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = ((x0 = y0) /\ (x1 = y1))) x2.
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := fun y0 : list a0 => ((@cons a0 x0 x2) = (@cons a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := forall y0 : list a0, ((@cons a0 x0 x2) = (@cons a0 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : list a0) := @eq Prop ((@cons a0 x0 x1) = (@cons a0 x2 x3)).
Definition term11 (a0 : Type') := fun y0 : list a0 => True.
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term3 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : a0, forall y1 : list a0, ((@cons a0 x0 x1) = (@cons a0 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) (x3 : list a0) := (x0 = x1) /\ (x2 = x3).
Definition term17 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, ((@cons a0 x0 y1) = (@cons a0 y0 y2)) = ((x0 = y0) /\ (y1 = y2)).
