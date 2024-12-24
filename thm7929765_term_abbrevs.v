Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term4 (a0 : Type') (x0 : type39 a0) (x1 : type6 a0) := @_mk_tybit1 a0 (x0 x1).
Definition term1 (a0 : Type') := fun y0 : type6 a0 => @_mk_tybit1 a0 ((fun y1 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y1 (fun y2 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y0).
Definition term3 (a0 : Type') (x0 : type39 a0) (x1 : type6 a0) := (fun y0 : type6 a0 => @_mk_tybit1 a0 (x0 y0)) x1.
Definition term2 (a0 : Type') (x0 : type39 a0) := fun y0 : type6 a0 => @_mk_tybit1 a0 (x0 y0).
Definition term5 (a0 : Type') (x0 : type6 a0) := @eq (tybit1 a0) (@_103802 a0 x0).
