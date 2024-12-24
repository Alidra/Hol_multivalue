Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : type1470 a0 a1) := @COND a0 (exists y0 : a0, x0 x1 y0) (@_MATCH a1 a0 x1 x0) (@_MATCH a1 a0 x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1470 a0 a1) (x2 : type1470 a0 a1) := @_MATCH a1 a0 x0 (@_SEQPATTERN a0 a1 x1 x2).
