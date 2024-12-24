Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1) (x2 : a1) := (x0 = (@EMPTY a0)) /\ (x1 = x2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a1) (x2 : a0 -> Prop) (x3 : a1) := @FINREC a0 a1 x0 x1 x2 x3 (NUMERAL 0).
