Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (fun y1 : nat => @BOTTOM a0).