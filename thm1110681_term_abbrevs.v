Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0) (x1 : type1402 a0) (x2 : list a0) := (fun y0 : list a0 => (@List.ForallOrdPairs a0 x1 (@cons a0 x0 y0)) = ((@List.Forall a0 (x1 x0) y0) /\ (@List.ForallOrdPairs a0 x1 y0))) x2.
Definition term2 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : list a0, (@List.ForallOrdPairs a0 y0 (@cons a0 x0 y1)) = ((@List.Forall a0 (y0 x0) y1) /\ (@List.ForallOrdPairs a0 y0 y1))) x1.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : type1402 a0, forall y1 : list a0, (@List.ForallOrdPairs a0 y0 (@cons a0 x0 y1)) = ((@List.Forall a0 (y0 x0) y1) /\ (@List.ForallOrdPairs a0 y0 y1)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : type1402 a0) := forall y0 : list a0, (@List.ForallOrdPairs a0 x1 (@cons a0 x0 y0)) = ((@List.Forall a0 (x1 x0) y0) /\ (@List.ForallOrdPairs a0 x1 y0)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1402 a0, forall y2 : list a0, (@List.ForallOrdPairs a0 y1 (@cons a0 y0 y2)) = ((@List.Forall a0 (y1 y0) y2) /\ (@List.ForallOrdPairs a0 y1 y2))) x0.
