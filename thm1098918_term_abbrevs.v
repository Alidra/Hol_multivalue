Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.removelast a0 (@cons a0 y0 y1)) = (@COND (list a0) (y1 = (@nil a0)) (@nil a0) (@cons a0 y0 (@List.removelast a0 y1))).
