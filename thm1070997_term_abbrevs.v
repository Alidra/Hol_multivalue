Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : recspace a0) := @eq (list a0) (@_mk_list a0 x0).
Definition term4 (a0 : Type') := @_mk_list a0 (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)).
Definition term3 (a0 : Type') := (fun y0 : recspace a0 => @_mk_list a0 y0) (@CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0)).
Definition term0 (a0 : Type') := fun y0 : recspace a0 => @_mk_list a0 y0.
Definition term5 (a0 : Type') (x0 : recspace a0) := @eq (list a0) ((fun y0 : recspace a0 => @_mk_list a0 y0) x0).
Definition term2 (a0 : Type') (x0 : recspace a0) := (fun y0 : recspace a0 => @_mk_list a0 y0) x0.
Definition term1 (a0 : Type') := @CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).
