Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2)).
Definition term2 (a0 : Type') := (forall y0 : list a0, (@List.app a0 (@nil a0) y0) = y0) /\ (forall y0 : a0, forall y1 : list a0, forall y2 : list a0, (@List.app a0 (@cons a0 y0 y1) y2) = (@cons a0 y0 (@List.app a0 y1 y2))).
Definition term1 (a0 : Type') := forall y0 : list a0, (@List.app a0 (@nil a0) y0) = y0.
