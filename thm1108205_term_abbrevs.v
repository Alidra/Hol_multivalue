Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : a1, forall y1 : type1474 a0 a1 a2, forall y2 : list a1, forall y3 : list a2, forall y4 : a0, (@ITLIST2 a0 a1 a2 y1 (@cons a1 y0 y2) y3 y4) = (y1 y0 (@hd a2 y3) (@ITLIST2 a0 a1 a2 y1 y2 (@tl a2 y3) y4)).
