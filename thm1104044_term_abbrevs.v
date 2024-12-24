Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : list a1) := (fun y0 : list a1 => (@ALL2 a0 a1 x0 (@nil a0) y0) = (y0 = (@nil a1))) x1.
