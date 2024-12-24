Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : list a0) := forall y0 : a0, (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0))).
Definition term2 (a0 : Type') (x0 : list a0) (x1 : a0) := (fun y0 : a0 => (@List.rev a0 (@cons a0 y0 x0)) = (@List.app a0 (@List.rev a0 x0) (@cons a0 y0 (@nil a0)))) x1.
Definition term0 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0)))) x0.
