Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') := fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term1 (a0 : Type') := fun y0 : type39 a0 => fun y1 : type1675 a0 => forall y2 : type1329 a0, (forall y3 : type1675 a0, (exists y4 : type6 a0, y3 = (y0 y4)) -> y2 y3) -> y2 y1.
Definition term4 (a0 : Type') := (fun y0 : type39 a0 => fun y1 : type1675 a0 => forall y2 : type1329 a0, (forall y3 : type1675 a0, (exists y4 : type6 a0, y3 = (y0 y4)) -> y2 y3) -> y2 y1) (fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))).
Definition term7 (a0 : Type') (x0 : type39 a0) := @eq ((recspace (finite_sum (finite_sum a0 a0) unit)) -> Prop) (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x0 y3)) -> y1 y2) -> y1 y0).
Definition term6 (a0 : Type') (x0 : type39 a0) := @eq ((recspace (finite_sum (finite_sum a0 a0) unit)) -> Prop) ((fun y0 : type39 a0 => fun y1 : type1675 a0 => forall y2 : type1329 a0, (forall y3 : type1675 a0, (exists y4 : type6 a0, y3 = (y0 y4)) -> y2 y3) -> y2 y1) x0).
Definition term3 (a0 : Type') (x0 : type39 a0) := (fun y0 : type39 a0 => fun y1 : type1675 a0 => forall y2 : type1329 a0, (forall y3 : type1675 a0, (exists y4 : type6 a0, y3 = (y0 y4)) -> y2 y3) -> y2 y1) x0.
Definition term5 (a0 : Type') := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0.
Definition term0 (a0 : Type') (x0 : type39 a0) := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x0 y3)) -> y1 y2) -> y1 y0.