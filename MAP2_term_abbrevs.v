Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : a1) (x2 : a0) := @cons a2 (x0 x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) := @eq (list a2) (@MAP2 a2 a1 a0 x0 (@nil a1) (@nil a0)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : a1) (x2 : a0) (x3 : list a0) := @cons a2 (x0 x1 (@hd a0 (@cons a0 x2 x3))).
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : a1) (x2 : list a1) (x3 : a0) (x4 : list a0) := @MAP2 a2 a1 a0 x0 (@cons a1 x1 x2) (@cons a0 x3 x4).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1469 a0 a1 a2) (x2 : list a1) (x3 : list a0) := @cons a2 (x1 x0 (@hd a0 x3)) (@MAP2 a2 a1 a0 x1 x2 (@tl a0 x3)).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1475 a0 a1 a2) (x2 : list a1) (x3 : list a2) := @cons a0 (x1 x0 (@hd a2 x3)) (@MAP2 a0 a1 a2 x1 x2 (@tl a2 x3)).
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : a1) (x2 : a0) (x3 : list a0) := x0 x1 (@hd a0 (@cons a0 x2 x3)).
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : a0) (x2 : type1469 a0 a1 a2) (x3 : list a1) (x4 : list a0) := ((@MAP2 a2 a1 a0 x2 (@nil a1) (@nil a0)) = (@nil a2)) /\ ((@MAP2 a2 a1 a0 x2 (@cons a1 x0 x3) (@cons a0 x1 x4)) = (@cons a2 (x2 x0 x1) (@MAP2 a2 a1 a0 x2 x3 x4))).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : a1) (x2 : list a1) (x3 : list a0) := @MAP2 a2 a1 a0 x0 (@cons a1 x1 x2) x3.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1475 a0 a1 a2) (x1 : a1) (x2 : list a1) (x3 : list a2) := @MAP2 a0 a1 a2 x0 (@cons a1 x1 x2) x3.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) := and ((@MAP2 a2 a1 a0 x0 (@nil a1) (@nil a0)) = (@nil a2)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : a0) (x2 : type1469 a0 a1 a2) (x3 : list a1) (x4 : list a0) := @eq (list a2) (@cons a2 (x2 x0 x1) (@MAP2 a2 a1 a0 x2 x3 x4)).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : a0) (x2 : type1469 a0 a1 a2) (x3 : list a1) (x4 : list a0) := @cons a2 (x2 x0 x1) (@MAP2 a2 a1 a0 x2 x3 x4).
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : list a1) (x2 : a0) (x3 : list a0) := @MAP2 a2 a1 a0 x0 x1 (@tl a0 (@cons a0 x2 x3)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1469 a0 a1 a2) (x2 : list a1) (x3 : a0) (x4 : list a0) := @cons a2 (x1 x0 (@hd a0 (@cons a0 x3 x4))) (@MAP2 a2 a1 a0 x1 x2 (@tl a0 (@cons a0 x3 x4))).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1469 a0 a1 a2) (x1 : a1) (x2 : list a1) (x3 : a0) (x4 : list a0) := @eq (list a2) (@MAP2 a2 a1 a0 x0 (@cons a1 x1 x2) (@cons a0 x3 x4)).
