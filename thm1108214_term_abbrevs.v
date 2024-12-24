Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1474 a0 a1 a2) (x1 : list a2) (x2 : a0) := (fun y0 : a0 => (@ITLIST2 a0 a1 a2 x0 (@nil a1) x1 y0) = y0) x2.
