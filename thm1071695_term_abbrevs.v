Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : type1399 a0) (x1 : a0) := fun y0 : list a0 => @_mk_list a0 (x0 x1 (@_dest_list a0 y0)).
Definition term7 (a0 : Type') (x0 : type1399 a0) (x1 : a0) (x2 : list a0) := @_mk_list a0 (x0 x1 (@_dest_list a0 x2)).
Definition term0 (a0 : Type') := fun y0 : a0 => fun y1 : recspace a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (@FCONS (recspace a0) y1 (fun y2 : nat => @BOTTOM a0)).
Definition term6 (a0 : Type') (x0 : type1399 a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => @_mk_list a0 (x0 x1 (@_dest_list a0 y0))) x2.
Definition term2 (a0 : Type') (x0 : type1399 a0) := fun y0 : a0 => fun y1 : list a0 => @_mk_list a0 (x0 y0 (@_dest_list a0 y1)).
Definition term5 (a0 : Type') (x0 : a0) := @eq ((list a0) -> list a0) (@cons a0 x0).
Definition term3 (a0 : Type') (x0 : type1399 a0) (x1 : a0) := (fun y0 : a0 => fun y1 : list a0 => @_mk_list a0 (x0 y0 (@_dest_list a0 y1))) x1.
Definition term1 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => @_mk_list a0 ((fun y2 : a0 => fun y3 : recspace a0 => @CONSTR a0 (S (NUMERAL 0)) y2 (@FCONS (recspace a0) y3 (fun y4 : nat => @BOTTOM a0))) y0 (@_dest_list a0 y1)).
Definition term8 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq (list a0) (@cons a0 x0 x1).
