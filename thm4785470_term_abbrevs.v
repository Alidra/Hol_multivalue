Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@set_of_list a0 (@cons a0 x0 y0)) = (@INSERT a0 x0 (@set_of_list a0 y0))) x1.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@set_of_list a0 (@cons a0 x0 y0)) = (@INSERT a0 x0 (@set_of_list a0 y0)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@set_of_list a0 (@cons a0 y0 y1)) = (@INSERT a0 y0 (@set_of_list a0 y1))) x0.
