Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : a0 => fun y1 : recspace a0 => @CONSTR a0 (S (NUMERAL 0)) y0 (@FCONS (recspace a0) y1 (fun y2 : nat => @BOTTOM a0)).
Definition term1 (a0 : Type') (x0 : recspace a0) (x1 : type1399 a0) := fun y0 : recspace a0 => forall y1 : type1338 a0, (forall y2 : recspace a0, ((y2 = x0) \/ (exists y3 : a0, exists y4 : recspace a0, (y2 = (x1 y3 y4)) /\ (y1 y4))) -> y1 y2) -> y1 y0.
Definition term3 (a0 : Type') (x0 : recspace a0) := @_dest_list a0 (@_mk_list a0 x0).
Definition term2 (a0 : Type') := @CONSTR a0 (NUMERAL 0) (@ε a0 (fun y0 : a0 => True)) (fun y0 : nat => @BOTTOM a0).