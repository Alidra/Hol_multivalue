Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1479 a0 a1) (x1 : a1) := @_mk_sum a0 a1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1) := @eq (Datatypes.sum a0 a1) (@inr a0 a1 x0).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a1 => @CONSTR (prod a0 a1) (S (NUMERAL 0)) (@pair a0 a1 (@ε a0 (fun y1 : a0 => True)) y0) (fun y1 : nat => @BOTTOM (prod a0 a1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1479 a0 a1) (x1 : a1) := (fun y0 : a1 => @_mk_sum a0 a1 (x0 y0)) x1.
