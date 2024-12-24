Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : list a1) := @cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 (@cons a1 x1 x2))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : a2) (x1 : a3) (x2 : list a2) (x3 : list a3) := ((@ZIP a0 a1 (@nil a0) (@nil a1)) = (@nil (prod a0 a1))) /\ ((@ZIP a2 a3 (@cons a2 x0 x2) (@cons a3 x1 x3)) = (@cons (prod a2 a3) (@pair a2 a3 x0 x1) (@ZIP a2 a3 x2 x3))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : list a0) (x1 : a1) (x2 : list a1) := @ZIP a0 a1 x0 (@tl a1 (@cons a1 x1 x2)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : a1) (x3 : list a1) := @eq (list (prod a0 a1)) (@ZIP a0 a1 (@cons a0 x0 x1) (@cons a1 x2 x3)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : a1) (x3 : list a1) := @ZIP a0 a1 (@cons a0 x0 x1) (@cons a1 x2 x3).
Definition term0 (a0 : Type') (a1 : Type') := @eq (list (prod a0 a1)) (@ZIP a0 a1 (@nil a0) (@nil a1)).
Definition term10 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : list a1) := @pair a0 a1 x0 (@hd a1 (@cons a1 x1 x2)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : list a0) (x3 : list a1) := @eq (list (prod a0 a1)) (@cons (prod a0 a1) (@pair a0 a1 x0 x1) (@ZIP a0 a1 x2 x3)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : list a1) := @cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 x2)) (@ZIP a0 a1 x1 (@tl a1 x2)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : list a1) := @ZIP a0 a1 (@cons a0 x0 x1) x2.
Definition term1 (a0 : Type') (a1 : Type') := and ((@ZIP a0 a1 (@nil a0) (@nil a1)) = (@nil (prod a0 a1))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : a1) (x3 : list a1) := @cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 (@cons a1 x2 x3))) (@ZIP a0 a1 x1 (@tl a1 (@cons a1 x2 x3))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : list a0) (x3 : list a1) := @cons (prod a0 a1) (@pair a0 a1 x0 x1) (@ZIP a0 a1 x2 x3).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @cons (prod a0 a1) (@pair a0 a1 x0 x1).
