Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') := @_mk_option a0 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)).
Definition term0 (a0 : Type') := @CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).