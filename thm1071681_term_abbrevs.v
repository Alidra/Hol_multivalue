Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => @_mk_list a0 ((fun y2 : a0 => fun y3 : recspace a0 => @CONSTR a0 (S (NUMERAL 0)) y2 (@FCONS (recspace a0) y3 (fun y4 : nat => @BOTTOM a0))) y0 (@_dest_list a0 y1)).