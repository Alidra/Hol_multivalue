Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : type6 a0 => @_mk_tybit1 a0 ((fun y1 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y1 (fun y2 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y0).
