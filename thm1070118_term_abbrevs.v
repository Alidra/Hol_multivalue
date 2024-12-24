Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') := fun y0 : a0 => @_mk_option a0 ((fun y1 : a0 => @CONSTR a0 (S (NUMERAL 0)) y1 (fun y2 : nat => @BOTTOM a0)) y0).
Definition term0 (a0 : Type') := fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0).
Definition term2 (a0 : Type') (x0 : type1432 a0) := fun y0 : a0 => @_mk_option a0 (x0 y0).
Definition term5 (a0 : Type') (x0 : a0) := @eq (option a0) (@Some a0 x0).
Definition term4 (a0 : Type') (x0 : type1432 a0) (x1 : a0) := @_mk_option a0 (x0 x1).
Definition term3 (a0 : Type') (x0 : type1432 a0) (x1 : a0) := (fun y0 : a0 => @_mk_option a0 (x0 y0)) x1.
