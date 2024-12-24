Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := ((@List.removelast a0 (@nil a0)) = (@nil a0)) /\ ((@List.removelast a0 (@cons a0 x0 x1)) = (@COND (list a0) (x1 = (@nil a0)) (@nil a0) (@cons a0 x0 (@List.removelast a0 x1)))).
Definition term0 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.removelast a0 (@cons a0 x0 x1).
Definition term1 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND (list a0) (x1 = (@nil a0)) (@nil a0) (@cons a0 x0 (@List.removelast a0 x1)).
