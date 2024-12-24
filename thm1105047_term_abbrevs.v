Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : a1, forall y1 : type1475 a0 a1 a2, forall y2 : list a1, forall y3 : list a2, (@MAP2 a0 a1 a2 y1 (@cons a1 y0 y2) y3) = (@cons a0 (y1 y0 (@hd a2 y3)) (@MAP2 a0 a1 a2 y1 y2 (@tl a2 y3))).
