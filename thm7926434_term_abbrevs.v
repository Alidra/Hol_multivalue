Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : finite_sum a0 a0 => @_mk_tybit0 a0 ((fun y1 : finite_sum a0 a0 => @CONSTR (finite_sum a0 a0) (NUMERAL 0) y1 (fun y2 : nat => @BOTTOM (finite_sum a0 a0))) y0).
