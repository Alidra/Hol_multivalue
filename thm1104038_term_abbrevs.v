Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : type1413 a0 a1, forall y2 : list a0, forall y3 : list a1, (@ALL2 a0 a1 y1 (@cons a0 y0 y2) y3) = (@COND Prop (y3 = (@nil a1)) False ((y1 y0 (@hd a1 y3)) /\ (@ALL2 a0 a1 y1 y2 (@tl a1 y3)))).
