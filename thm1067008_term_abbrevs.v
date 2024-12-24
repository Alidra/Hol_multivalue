Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') := fun y0 : a0 => @CONSTR (prod a0 a1) (NUMERAL 0) (@pair a0 a1 y0 (@ε a1 (fun y1 : a1 => True))) (fun y1 : nat => @BOTTOM (prod a0 a1)).
Definition term3 (a0 : Type') (a1 : Type') := (fun y0 : type1431 a0 a1 => fun y1 : a0 => @_mk_sum a0 a1 (y0 y1)) (fun y0 : a0 => @CONSTR (prod a0 a1) (NUMERAL 0) (@pair a0 a1 y0 (@ε a1 (fun y1 : a1 => True))) (fun y1 : nat => @BOTTOM (prod a0 a1))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) := (fun y0 : type1431 a0 a1 => fun y1 : a0 => @_mk_sum a0 a1 (y0 y1)) x0.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) := @eq (a0 -> Datatypes.sum a0 a1) ((fun y0 : type1431 a0 a1 => fun y1 : a0 => @_mk_sum a0 a1 (y0 y1)) x0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) := @eq (a0 -> Datatypes.sum a0 a1) (fun y0 : a0 => @_mk_sum a0 a1 (x0 y0)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) := fun y0 : a0 => @_mk_sum a0 a1 (x0 y0).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : type1431 a0 a1 => fun y1 : a0 => @_mk_sum a0 a1 (y0 y1).
Definition term4 (a0 : Type') (a1 : Type') := fun y0 : a0 => @_mk_sum a0 a1 ((fun y1 : a0 => @CONSTR (prod a0 a1) (NUMERAL 0) (@pair a0 a1 y1 (@ε a1 (fun y2 : a1 => True))) (fun y2 : nat => @BOTTOM (prod a0 a1))) y0).
