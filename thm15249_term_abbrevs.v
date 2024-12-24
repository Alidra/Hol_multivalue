Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) := @COND a0 (x0 = x0).
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) := @COND a0 (x0 = x0) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @eq a0 (@COND a0 (x0 = x0) x1 x2).
