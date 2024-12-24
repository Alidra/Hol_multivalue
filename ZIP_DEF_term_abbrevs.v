Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : list a1) := ((@ZIP a0 a1 (@nil a0) x2) = (@nil (prod a0 a1))) /\ ((@ZIP a0 a1 (@cons a0 x0 x1) x2) = (@cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 x2)) (@ZIP a0 a1 x1 (@tl a1 x2)))).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : list a1) := @cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 x2)) (@ZIP a0 a1 x1 (@tl a1 x2)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : list a1) := @ZIP a0 a1 (@cons a0 x0 x1) x2.
