Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : a2) (x2 : list a2) (x3 : a1) (x4 : list a1) (x5 : a0) := @ITLIST2 a0 a2 a1 x0 (@cons a2 x1 x2) (@cons a1 x3 x4) x5.
Definition term8 (a0 : Type') (x0 : a0) (x1 : list a0) := @hd a0 (@cons a0 x0 x1).
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2) (x1 : a1) (x2 : type1515 a0 a1 a2) (x3 : list a2) (x4 : list a1) (x5 : a0) := ((@ITLIST2 a0 a2 a1 x2 (@nil a2) (@nil a1) x5) = x5) /\ ((@ITLIST2 a0 a2 a1 x2 (@cons a2 x0 x3) (@cons a1 x1 x4) x5) = (x2 x0 x1 (@ITLIST2 a0 a2 a1 x2 x3 x4 x5))).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : a2) (x2 : list a2) (x3 : a1) (x4 : list a1) (x5 : a0) := @eq a0 (@ITLIST2 a0 a2 a1 x0 (@cons a2 x1 x2) (@cons a1 x3 x4) x5).
Definition term10 (a0 : Type') (x0 : a0) (x1 : list a0) := @tl a0 (@cons a0 x0 x1).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2) (x1 : type1515 a0 a1 a2) (x2 : list a2) (x3 : list a1) (x4 : a0) := x1 x0 (@hd a1 x3) (@ITLIST2 a0 a2 a1 x1 x2 (@tl a1 x3) x4).
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : list a2) (x2 : a1) (x3 : list a1) := @ITLIST2 a0 a2 a1 x0 x1 (@tl a1 (@cons a1 x2 x3)).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : a0) := @eq a0 (@ITLIST2 a0 a2 a1 x0 (@nil a2) (@nil a1) x1).
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2) (x1 : a1) (x2 : type1515 a0 a1 a2) (x3 : list a2) (x4 : list a1) (x5 : a0) := x2 x0 x1 (@ITLIST2 a0 a2 a1 x2 x3 x4 x5).
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2) (x1 : a1) (x2 : type1515 a0 a1 a2) (x3 : list a2) (x4 : list a1) (x5 : a0) := @eq a0 (x2 x0 x1 (@ITLIST2 a0 a2 a1 x2 x3 x4 x5)).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a2) (x1 : type1515 a0 a1 a2) (x2 : list a2) (x3 : a1) (x4 : list a1) (x5 : a0) := x1 x0 (@hd a1 (@cons a1 x3 x4)) (@ITLIST2 a0 a2 a1 x1 x2 (@tl a1 (@cons a1 x3 x4)) x5).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : a2) (x2 : list a2) (x3 : list a1) (x4 : a0) := @ITLIST2 a0 a2 a1 x0 (@cons a2 x1 x2) x3 x4.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) (x1 : a1) (x2 : list a1) (x3 : list a2) (x4 : a0) := @ITLIST2 a0 a1 a2 x0 (@cons a1 x1 x2) x3 x4.
Definition term9 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : a2) (x2 : a1) (x3 : list a1) := x0 x1 (@hd a1 (@cons a1 x2 x3)).
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : list a2) (x2 : a1) (x3 : list a1) (x4 : a0) := @ITLIST2 a0 a2 a1 x0 x1 (@tl a1 (@cons a1 x2 x3)) x4.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1515 a0 a1 a2) (x1 : a0) := and ((@ITLIST2 a0 a2 a1 x0 (@nil a2) (@nil a1) x1) = x1).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1474 a0 a1 a2) (x2 : list a1) (x3 : list a2) (x4 : a0) := x1 x0 (@hd a2 x3) (@ITLIST2 a0 a1 a2 x1 x2 (@tl a2 x3) x4).
