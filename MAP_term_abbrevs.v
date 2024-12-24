Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> a1, (@List.map a0 a1 y0 (@nil a0)) = (@nil a1)) /\ (forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (@List.map a0 a1 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (@List.map a0 a1 y0 y2))).
Definition term1 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (@List.map a0 a1 y0 (@nil a0)) = (@nil a1).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0, forall y2 : list a0, (@List.map a0 a1 y0 (@cons a0 y1 y2)) = (@cons a1 (y0 y1) (@List.map a0 a1 y0 y2)).
