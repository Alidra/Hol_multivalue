Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @List.app a0 (@cons a0 x0 x1) x2.
Definition term12 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (list a0) (@List.app a0 (@cons a0 x0 (@nil a0)) x1).
Definition term4 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a0, (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0)).
Definition term18 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1)).
Definition term23 (a0 : Type') := forall y0 : a0, True.
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2))) x0.
Definition term17 (a0 : Type') := forall y0 : list a0, True.
Definition term9 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (@List.app a0 (@nil a0) y0) = y0) x0.
Definition term14 (a0 : Type') (x0 : a0) := fun y0 : list a0 => (@List.app a0 (@cons a0 x0 (@nil a0)) y0) = (@cons a0 x0 y0).
Definition term20 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, (@List.app a0 (@cons a0 y0 (@nil a0)) y1) = (@cons a0 y0 y1).
Definition term21 (a0 : Type') := fun y0 : a0 => True.
Definition term8 (a0 : Type') := forall y0 : list a0, (@List.app a0 (@nil a0) y0) = y0.
Definition term16 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.app a0 (@cons a0 x0 (@nil a0)) y0) = (@cons a0 x0 y0).
Definition term10 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.app a0 (@cons a0 x0 (@nil a0)) x1.
Definition term7 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := @cons a0 x0 (@List.app a0 x1 x2).
Definition term3 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.app a0 (@cons a0 x0 y0) y1) = (@cons a0 x0 (@List.app a0 y0 y1))) x1.
Definition term11 (a0 : Type') (x0 : a0) (x1 : list a0) := @cons a0 x0 (@List.app a0 (@nil a0) x1).
Definition term15 (a0 : Type') := fun y0 : list a0 => True.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term5 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : list a0) := (fun y0 : list a0 => (@List.app a0 (@cons a0 x0 x1) y0) = (@cons a0 x0 (@List.app a0 x1 y0))) x2.
Definition term22 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.app a0 (@cons a0 y0 (@nil a0)) y1) = (@cons a0 y0 y1).
Definition term13 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (list a0) (@cons a0 x0 x1).
