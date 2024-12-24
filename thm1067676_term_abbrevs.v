Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) (x1 : a0) := @_mk_sum a0 a1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) := @eq (Datatypes.sum a0 a1) (@inl a0 a1 x0).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 => @CONSTR (prod a0 a1) (NUMERAL 0) (@pair a0 a1 y0 (@ε a1 (fun y1 : a1 => True))) (fun y1 : nat => @BOTTOM (prod a0 a1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1431 a0 a1) (x1 : a0) := (fun y0 : a0 => @_mk_sum a0 a1 (x0 y0)) x1.
