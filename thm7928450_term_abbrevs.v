Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : type1675 a0) := (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0) x0.
Definition term1 (a0 : Type') (x0 : type1675 a0) := @_dest_tybit1 a0 (@_mk_tybit1 a0 x0).
