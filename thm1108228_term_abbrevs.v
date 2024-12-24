Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) := forall y0 : type1474 a0 a1 a2, forall y1 : list a1, forall y2 : list a2, forall y3 : a0, (@ITLIST2 a0 a1 a2 y0 (@cons a1 x0 y1) y2 y3) = (y0 x0 (@hd a2 y2) (@ITLIST2 a0 a1 a2 y0 y1 (@tl a2 y2) y3)).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) (x2 : list a1) := forall y0 : list a2, forall y1 : a0, (@ITLIST2 a0 a1 a2 x1 (@cons a1 x0 x2) y0 y1) = (x1 x0 (@hd a2 y0) (@ITLIST2 a0 a1 a2 x1 x2 (@tl a2 y0) y1)).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) := forall y0 : list a1, forall y1 : list a2, forall y2 : a0, (@ITLIST2 a0 a1 a2 x1 (@cons a1 x0 y0) y1 y2) = (x1 x0 (@hd a2 y1) (@ITLIST2 a0 a1 a2 x1 y0 (@tl a2 y1) y2)).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1474 a0 a1 a2, forall y2 : list a1, forall y3 : list a2, forall y4 : a0, (@ITLIST2 a0 a1 a2 y1 (@cons a1 y0 y2) y3 y4) = (y1 y0 (@hd a2 y3) (@ITLIST2 a0 a1 a2 y1 y2 (@tl a2 y3) y4))) x0.
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) (x2 : list a1) := (fun y0 : list a1 => forall y1 : list a2, forall y2 : a0, (@ITLIST2 a0 a1 a2 x1 (@cons a1 x0 y0) y1 y2) = (x1 x0 (@hd a2 y1) (@ITLIST2 a0 a1 a2 x1 y0 (@tl a2 y1) y2))) x2.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) (x2 : list a1) (x3 : list a2) := (fun y0 : list a2 => forall y1 : a0, (@ITLIST2 a0 a1 a2 x1 (@cons a1 x0 x2) y0 y1) = (x1 x0 (@hd a2 y0) (@ITLIST2 a0 a1 a2 x1 x2 (@tl a2 y0) y1))) x3.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) := (fun y0 : type1474 a0 a1 a2 => forall y1 : list a1, forall y2 : list a2, forall y3 : a0, (@ITLIST2 a0 a1 a2 y0 (@cons a1 x0 y1) y2 y3) = (y0 x0 (@hd a2 y2) (@ITLIST2 a0 a1 a2 y0 y1 (@tl a2 y2) y3))) x1.
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) (x2 : list a1) (x3 : list a2) (x4 : a0) := (fun y0 : a0 => (@ITLIST2 a0 a1 a2 x1 (@cons a1 x0 x2) x3 y0) = (x1 x0 (@hd a2 x3) (@ITLIST2 a0 a1 a2 x1 x2 (@tl a2 x3) y0))) x4.
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) (x2 : list a1) (x3 : list a2) := forall y0 : a0, (@ITLIST2 a0 a1 a2 x1 (@cons a1 x0 x2) x3 y0) = (x1 x0 (@hd a2 x3) (@ITLIST2 a0 a1 a2 x1 x2 (@tl a2 x3) y0)).
