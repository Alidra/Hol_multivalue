Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : list a0) := (fun y0 : list a0 => (@FILTER a0 x1 (@cons a0 x0 y0)) = (@COND (list a0) (x1 x0) (@cons a0 x0 (@FILTER a0 x1 y0)) (@FILTER a0 x1 y0))) x2.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : list a0, (@FILTER a0 y0 (@cons a0 x0 y1)) = (@COND (list a0) (y0 x0) (@cons a0 x0 (@FILTER a0 y0 y1)) (@FILTER a0 y0 y1))) x1.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : list a0, (@FILTER a0 x1 (@cons a0 x0 y0)) = (@COND (list a0) (x1 x0) (@cons a0 x0 (@FILTER a0 x1 y0)) (@FILTER a0 x1 y0)).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : list a0, (@FILTER a0 y0 (@cons a0 x0 y1)) = (@COND (list a0) (y0 x0) (@cons a0 x0 (@FILTER a0 y0 y1)) (@FILTER a0 y0 y1)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : list a0, (@FILTER a0 y1 (@cons a0 y0 y2)) = (@COND (list a0) (y1 y0) (@cons a0 y0 (@FILTER a0 y1 y2)) (@FILTER a0 y1 y2))) x0.