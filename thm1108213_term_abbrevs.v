Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) (x1 : list a2) := forall y0 : a0, (@ITLIST2 a0 a1 a2 x0 (@nil a1) x1 y0) = y0.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1474 a0 a1 a2, forall y1 : list a2, forall y2 : a0, (@ITLIST2 a0 a1 a2 y0 (@nil a1) y1 y2) = y2.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) := forall y0 : list a2, forall y1 : a0, (@ITLIST2 a0 a1 a2 x0 (@nil a1) y0 y1) = y1.
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) (x1 : list a2) (x2 : a0) := (fun y0 : a0 => (@ITLIST2 a0 a1 a2 x0 (@nil a1) x1 y0) = y0) x2.
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) (x1 : list a2) := (fun y0 : list a2 => forall y1 : a0, (@ITLIST2 a0 a1 a2 x0 (@nil a1) y0 y1) = y1) x1.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) := (fun y0 : type1474 a0 a1 a2 => forall y1 : list a2, forall y2 : a0, (@ITLIST2 a0 a1 a2 y0 (@nil a1) y1 y2) = y2) x0.