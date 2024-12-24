Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : type1470 a0 a1 => fun y1 : type1470 a0 a1 => fun y2 : a1 => @COND (a0 -> Prop) (exists y3 : a0, y0 y2 y3) (y0 y2) (y1 y2).
