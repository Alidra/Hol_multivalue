Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1677 a0 a1) := @_dest_sum a0 a1 (@_mk_sum a0 a1 x0).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1677 a0 a1) := (fun y0 : type1677 a0 a1 => forall y1 : type1333 a0 a1, (forall y2 : type1677 a0 a1, ((exists y3 : a0, y2 = ((fun y4 : a0 => @CONSTR (prod a0 a1) (NUMERAL 0) (@pair a0 a1 y4 (@ε a1 (fun y5 : a1 => True))) (fun y5 : nat => @BOTTOM (prod a0 a1))) y3)) \/ (exists y3 : a1, y2 = ((fun y4 : a1 => @CONSTR (prod a0 a1) (S (NUMERAL 0)) (@pair a0 a1 (@ε a0 (fun y5 : a0 => True)) y4) (fun y5 : nat => @BOTTOM (prod a0 a1))) y3))) -> y1 y2) -> y1 y0) x0.
