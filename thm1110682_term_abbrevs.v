Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : list a0) := (fun y0 : list a0 => (@List.ForallOrdPairs a0 x1 (@cons a0 x0 y0)) = ((@List.Forall a0 (x1 x0) y0) /\ (@List.ForallOrdPairs a0 x1 y0))) x2.
Definition term1 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : list a0) := @List.ForallOrdPairs a0 x0 (@cons a0 x1 x2).
Definition term2 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : list a0) := (@List.Forall a0 (x1 x0) x2) /\ (@List.ForallOrdPairs a0 x1 x2).
