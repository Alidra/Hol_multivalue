Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1475 a0 a1 a2) (x1 : list a2) := (fun y0 : list a2 => (@MAP2 a0 a1 a2 x0 (@nil a1) y0) = (@nil a0)) x1.
