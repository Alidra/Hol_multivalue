Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := ((@LAST a0 (@cons a0 x0 (@nil a0))) = x0) /\ ((@LAST a0 (@cons a0 x0 (@cons a0 x1 x2))) = (@LAST a0 (@cons a0 x1 x2))).
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => ~ ((@cons a0 x0 y0) = (@nil a0))) x1.
Definition term6 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, ~ ((@cons a0 x0 y0) = (@nil a0)).
Definition term7 (a0 : Type') (x0 : a0) := @LAST a0 (@cons a0 x0 (@nil a0)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @LAST a0 (@cons a0 x0 (@cons a0 x1 x2)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, ~ ((@cons a0 y0 y1) = (@nil a0))) x0.
Definition term19 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq a0 (@COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1)).
Definition term5 (a0 : Type') (x0 : a0) (x1 : list a0) := @LAST a0 (@cons a0 x0 x1).
Definition term8 (a0 : Type') (x0 : a0) := @COND a0 ((@nil a0) = (@nil a0)) x0 (@LAST a0 (@nil a0)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term4 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> ((@cons a0 x0 x1) = (@nil a0)) = False.
Definition term12 (a0 : Type') (x0 : a0) := and ((@LAST a0 (@cons a0 x0 (@nil a0))) = x0).
Definition term11 (a0 : Type') (x0 : a0) := @eq a0 (@LAST a0 (@cons a0 x0 (@nil a0))).
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @eq a0 (@LAST a0 (@cons a0 x0 (@cons a0 x1 x2))).
Definition term10 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @COND a0 ((@cons a0 x1 x2) = (@nil a0)) x0 (@LAST a0 (@cons a0 x1 x2)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @COND a0 False x0 (@COND a0 (x2 = (@nil a0)) x1 (@LAST a0 x2)).
Definition term15 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND a0 ((@cons a0 x0 x1) = (@nil a0)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) := @COND a0 ((@cons a0 x0 x1) = (@nil a0)) x2.
