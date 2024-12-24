Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : list a0, forall y1 : a0, (@List.rev a0 (@cons a0 y1 y0)) = (@List.app a0 (@List.rev a0 y0) (@cons a0 y1 (@nil a0))).
