Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : list a1) (x3 : list a0) := @ALLPAIRS a0 a1 x0 (@cons a1 x1 x2) x3.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) (x3 : list a0) := (@List.Forall a0 (x1 x0) x3) /\ (@ALLPAIRS a0 a1 x1 x2 x3).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : list a1) (x3 : list a0) := ((@ALLPAIRS a0 a1 x1 (@nil a1) x3) = True) /\ ((@ALLPAIRS a0 a1 x1 (@cons a1 x0 x2) x3) = ((@List.Forall a0 (x1 x0) x3) /\ (@ALLPAIRS a0 a1 x1 x2 x3))).
