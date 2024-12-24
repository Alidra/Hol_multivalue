Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := ((@List.In a0 x1 (@nil a0)) = False) /\ ((@List.In a0 x1 (@cons a0 x0 x2)) = ((x1 = x0) \/ (@List.In a0 x1 x2))).
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := (x1 = x0) \/ (@List.In a0 x1 x2).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : list a0) := @List.In a0 x0 (@cons a0 x1 x2).
