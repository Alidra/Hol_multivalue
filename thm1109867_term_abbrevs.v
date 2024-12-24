Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a1, forall y1 : type1470 a0 a1, forall y2 : list a1, forall y3 : list a0, (@ALLPAIRS a0 a1 y1 (@cons a1 y0 y2) y3) = ((@List.Forall a0 (y1 y0) y3) /\ (@ALLPAIRS a0 a1 y1 y2 y3)).
