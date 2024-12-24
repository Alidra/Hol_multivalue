Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : list a1, (@ZIP a0 a1 (@nil a0) y0) = (@nil (prod a0 a1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : list a1) := (fun y0 : list a1 => (@ZIP a0 a1 (@nil a0) y0) = (@nil (prod a0 a1))) x0.
