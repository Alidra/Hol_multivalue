Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a1, (@ZIP a0 a1 (@cons a0 y0 y1) y2) = (@cons (prod a0 a1) (@pair a0 a1 y0 (@hd a1 y2)) (@ZIP a0 a1 y1 (@tl a1 y2))).
