Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (a0 : Type') (a1 : Type') (x0 : list a1) (x1 : type1467 a0 a1) (x2 : a1) (x3 : a0) := @ITLIST a0 a1 x1 x0 (@ITLIST a0 a1 x1 (@cons a1 x2 (@nil a1)) x3).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) := forall y0 : a0, forall y1 : list a1, forall y2 : list a1, (@ITLIST a0 a1 x0 (@List.app a1 y1 y2) y0) = (@ITLIST a0 a1 x0 y1 (@ITLIST a0 a1 x0 y2 y0)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1467 a0 a1) (x2 : a0) := x1 x0 (@ITLIST a0 a1 x1 (@nil a1) x2).
Definition term15 (a0 : Type') (a1 : Type') (x0 : list a1) (x1 : type1467 a0 a1) (x2 : a1) (x3 : a0) := @ITLIST a0 a1 x1 x0 (x1 x2 x3).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : list a1) (x2 : a1) (x3 : a0) := @ITLIST a0 a1 x0 (@List.app a1 x1 (@cons a1 x2 (@nil a1))) x3.
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a0) := forall y0 : list a1, forall y1 : list a1, (@ITLIST a0 a1 x0 (@List.app a1 y0 y1) x1) = (@ITLIST a0 a1 x0 y0 (@ITLIST a0 a1 x0 y1 x1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) := (fun y0 : type1467 a0 a1 => forall y1 : a0, forall y2 : list a1, forall y3 : list a1, (@ITLIST a0 a1 y0 (@List.app a1 y2 y3) y1) = (@ITLIST a0 a1 y0 y2 (@ITLIST a0 a1 y0 y3 y1))) x0.
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a1) (x2 : a0) := @ITLIST a0 a1 x0 (@cons a1 x1 (@nil a1)) x2.
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a1) (x2 : a0) := fun y0 : list a1 => (@ITLIST a0 a1 x0 (@List.app a1 y0 (@cons a1 x1 (@nil a1))) x2) = (@ITLIST a0 a1 x0 y0 (x0 x1 x2)).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : list a1) (x2 : a1) (x3 : a0) := @eq a0 (@ITLIST a0 a1 x0 (@List.app a1 x1 (@cons a1 x2 (@nil a1))) x3).
Definition term21 (a0 : Type') := forall y0 : list a0, True.
Definition term8 (a0 : Type') (a1 : Type') (x0 : list a1) (x1 : type1467 a0 a1) (x2 : list a1) (x3 : a0) := @ITLIST a0 a1 x1 x0 (@ITLIST a0 a1 x1 x2 x3).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1467 a0 a1) (x2 : list a1) (x3 : a0) := x1 x0 (@ITLIST a0 a1 x1 x2 x3).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a0) := (fun y0 : a0 => forall y1 : list a1, forall y2 : list a1, (@ITLIST a0 a1 x0 (@List.app a1 y1 y2) y0) = (@ITLIST a0 a1 x0 y1 (@ITLIST a0 a1 x0 y2 y0))) x1.
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a1) (x2 : a0) := forall y0 : list a1, (@ITLIST a0 a1 x0 (@List.app a1 y0 (@cons a1 x1 (@nil a1))) x2) = (@ITLIST a0 a1 x0 y0 (x0 x1 x2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : list a1) (x1 : type1467 a0 a1) (x2 : a0) := forall y0 : list a1, (@ITLIST a0 a1 x1 (@List.app a1 x0 y0) x2) = (@ITLIST a0 a1 x1 x0 (@ITLIST a0 a1 x1 y0 x2)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : list a1) (x1 : type1467 a0 a1) (x2 : a1) (x3 : a0) := @eq a0 (@ITLIST a0 a1 x1 x0 (x1 x2 x3)).
Definition term19 (a0 : Type') := fun y0 : list a0 => True.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a1) (x2 : list a1) (x3 : a0) := @ITLIST a0 a1 x0 (@cons a1 x1 x2) x3.
Definition term6 (a0 : Type') (a1 : Type') (x0 : list a1) (x1 : type1467 a0 a1) (x2 : a0) (x3 : list a1) := (fun y0 : list a1 => (@ITLIST a0 a1 x1 (@List.app a1 x0 y0) x2) = (@ITLIST a0 a1 x1 x0 (@ITLIST a0 a1 x1 y0 x2))) x3.
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : list a1) (x2 : list a1) (x3 : a0) := @ITLIST a0 a1 x0 (@List.app a1 x1 x2) x3.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a0) (x2 : list a1) := (fun y0 : list a1 => forall y1 : list a1, (@ITLIST a0 a1 x0 (@List.app a1 y0 y1) x1) = (@ITLIST a0 a1 x0 y0 (@ITLIST a0 a1 x0 y1 x1))) x2.
