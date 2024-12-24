Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : type1676 a0) := (fun y0 : type1676 a0 => forall y1 : type1331 a0, (forall y2 : type1676 a0, (exists y3 : finite_sum a0 a0, y2 = ((fun y4 : finite_sum a0 a0 => @CONSTR (finite_sum a0 a0) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum a0 a0))) y3)) -> y1 y2) -> y1 y0) x0.
Definition term1 (a0 : Type') (x0 : type45 a0) := fun y0 : type1676 a0 => forall y1 : type1331 a0, (forall y2 : type1676 a0, (exists y3 : finite_sum a0 a0, y2 = (x0 y3)) -> y1 y2) -> y1 y0.
Definition term0 (a0 : Type') := fun y0 : finite_sum a0 a0 => @CONSTR (finite_sum a0 a0) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum a0 a0)).
