Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : recspace a0) := (fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y3 : a0 => True)) (fun y3 : nat => @BOTTOM a0))) \/ (exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR a0 (S (NUMERAL 0)) y4 (fun y5 : nat => @BOTTOM a0)) y3))) -> y1 y2) -> y1 y0) x0.
Definition term1 (a0 : Type') (x0 : recspace a0) := @_dest_option a0 (@_mk_option a0 x0).
