Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : tybit1 a0) := ((@_dest_tybit1 a0 x2) = (@_dest_tybit1 a0 x2)) -> (fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0))) (@_dest_tybit1 a0 x2).
Definition term32 (a0 : Type') (x0 : tybit1 a0) := imp ((@_dest_tybit1 a0 x0) = (@_dest_tybit1 a0 x0)).
Definition term13 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type1351 a0) (x3 : type6 a0) := (x0 (x1 x3)) /\ (x2 (@_103802 a0 x3)).
Definition term8 (a0 : Type') := fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term4 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : type39 a0) (x3 : type6 a0) := (fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0))) (x2 x3).
Definition term6 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type6 a0) := (fun y0 : type6 a0 => x0 (x1 y0)) x2.
Definition term34 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : tybit1 a0) := (x0 (@_dest_tybit1 a0 x2)) /\ (x1 (@_mk_tybit1 a0 (@_dest_tybit1 a0 x2))).
Definition term17 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : type39 a0) := forall y0 : type6 a0, (fun y1 : type1675 a0 => (x0 y1) /\ (x1 (@_mk_tybit1 a0 y1))) (x2 y0).
Definition term31 (a0 : Type') (x0 : tybit1 a0) := @eq (recspace (finite_sum (finite_sum a0 a0) unit)) (@_dest_tybit1 a0 x0).
Definition term41 (a0 : Type') (x0 : type1329 a0) := ((fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) = (fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))) -> (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0)) -> forall y0 : type1351 a0, (forall y1 : type6 a0, y0 (@_103802 a0 y1)) -> forall y1 : tybit1 a0, y0 y1.
Definition term23 (a0 : Type') (x0 : type1329 a0) (x1 : tybit1 a0) := x0 (@_dest_tybit1 a0 x1).
Definition term36 (a0 : Type') (x0 : type1351 a0) := forall y0 : tybit1 a0, x0 y0.
Definition term27 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : tybit1 a0) := (fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0))) (@_dest_tybit1 a0 x2).
Definition term35 (a0 : Type') (x0 : type1351 a0) (x1 : tybit1 a0) := x0 (@_mk_tybit1 a0 (@_dest_tybit1 a0 x1)).
Definition term15 (a0 : Type') (x0 : type1351 a0) := forall y0 : type6 a0, x0 (@_103802 a0 y0).
Definition term28 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : tybit1 a0) := ((@_dest_tybit1 a0 (@_mk_tybit1 a0 (@_dest_tybit1 a0 x2))) = (@_dest_tybit1 a0 x2)) -> (fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0))) (@_dest_tybit1 a0 x2).
Definition term19 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) := forall y0 : type1675 a0, (x0 y0) -> (fun y1 : type1675 a0 => (x0 y1) /\ (x1 (@_mk_tybit1 a0 y1))) y0.
Definition term9 (a0 : Type') (x0 : type39 a0) (x1 : type6 a0) := @_mk_tybit1 a0 (x0 x1).
Definition term21 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : tybit1 a0) := (x0 (@_dest_tybit1 a0 x2)) -> (fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0))) (@_dest_tybit1 a0 x2).
Definition term2 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) := fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0)).
Definition term26 (a0 : Type') (x0 : tybit1 a0) := imp ((@_dest_tybit1 a0 (@_mk_tybit1 a0 (@_dest_tybit1 a0 x0))) = (@_dest_tybit1 a0 x0)).
Definition term43 (a0 : Type') := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0.
Definition term0 (a0 : Type') (x0 : type39 a0) := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x0 y3)) -> y1 y2) -> y1 y0.
Definition term24 (a0 : Type') (x0 : tybit1 a0) := @_dest_tybit1 a0 (@_mk_tybit1 a0 (@_dest_tybit1 a0 x0)).
Definition term37 (a0 : Type') (x0 : type1351 a0) := (forall y0 : type6 a0, x0 (@_103802 a0 y0)) -> forall y0 : tybit1 a0, x0 y0.
Definition term30 (a0 : Type') (x0 : tybit1 a0) := @eq (recspace (finite_sum (finite_sum a0 a0) unit)) (@_dest_tybit1 a0 (@_mk_tybit1 a0 (@_dest_tybit1 a0 x0))).
Definition term5 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : type39 a0) (x3 : type6 a0) := (x0 (x2 x3)) /\ (x1 (@_mk_tybit1 a0 (x2 x3))).
Definition term42 (a0 : Type') (x0 : type1329 a0) := (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0)) -> forall y0 : type1351 a0, (forall y1 : type6 a0, y0 (@_103802 a0 y1)) -> forall y1 : tybit1 a0, y0 y1.
Definition term39 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) := (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x1 y3)) -> y1 y2) -> y1 y0)) -> forall y0 : type1351 a0, (forall y1 : type6 a0, y0 (@_103802 a0 y1)) -> forall y1 : tybit1 a0, y0 y1.
Definition term29 (a0 : Type') (x0 : tybit1 a0) := @_mk_tybit1 a0 (@_dest_tybit1 a0 x0).
Definition term44 (a0 : Type') := ((fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0) = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0)) -> forall y0 : type1351 a0, (forall y1 : type6 a0, y0 (@_103802 a0 y1)) -> forall y1 : tybit1 a0, y0 y1.
Definition term10 (a0 : Type') (x0 : type1351 a0) (x1 : type39 a0) (x2 : type6 a0) := x0 (@_mk_tybit1 a0 (x1 x2)).
Definition term20 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : tybit1 a0) := (fun y0 : type1675 a0 => (x0 y0) -> (fun y1 : type1675 a0 => (x0 y1) /\ (x1 (@_mk_tybit1 a0 y1))) y0) (@_dest_tybit1 a0 x2).
Definition term25 (a0 : Type') (x0 : type1329 a0) (x1 : tybit1 a0) := imp (x0 (@_dest_tybit1 a0 x1)).
Definition term18 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : type39 a0) := (forall y0 : type6 a0, x1 (@_103802 a0 y0)) -> forall y0 : type6 a0, (fun y1 : type1675 a0 => (x0 y1) /\ (x1 (@_mk_tybit1 a0 y1))) (x2 y0).
Definition term16 (a0 : Type') (x0 : type1351 a0) (x1 : type6 a0) := (fun y0 : type6 a0 => x0 (@_103802 a0 y0)) x1.
Definition term14 (a0 : Type') (x0 : type1329 a0) (x1 : type1351 a0) (x2 : type39 a0) (x3 : type6 a0) := @eq Prop ((fun y0 : type1675 a0 => (x0 y0) /\ (x1 (@_mk_tybit1 a0 y0))) (x2 x3)).
Definition term40 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) := (x1 = (fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))) -> (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x1 y3)) -> y1 y2) -> y1 y0)) -> forall y0 : type1351 a0, (forall y1 : type6 a0, y0 (@_103802 a0 y1)) -> forall y1 : tybit1 a0, y0 y1.
Definition term38 (a0 : Type') := forall y0 : type1351 a0, (forall y1 : type6 a0, y0 (@_103802 a0 y1)) -> forall y1 : tybit1 a0, y0 y1.
Definition term1 (a0 : Type') (x0 : type39 a0) (x1 : type1329 a0) (x2 : type1351 a0) := (fun y0 : type1329 a0 => (forall y1 : type6 a0, y0 (x0 y1)) -> forall y1 : type1675 a0, (x1 y1) -> y0 y1) (fun y0 : type1675 a0 => (x1 y0) /\ (x2 (@_mk_tybit1 a0 y0))).
Definition term22 (a0 : Type') (x0 : type1675 a0) := @_dest_tybit1 a0 (@_mk_tybit1 a0 x0).
Definition term7 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type6 a0) := x0 (x1 x2).
Definition term3 (a0 : Type') (x0 : type39 a0) (x1 : type1329 a0) (x2 : type1351 a0) := (forall y0 : type6 a0, (fun y1 : type1675 a0 => (x1 y1) /\ (x2 (@_mk_tybit1 a0 y1))) (x0 y0)) -> forall y0 : type1675 a0, (x1 y0) -> (fun y1 : type1675 a0 => (x1 y1) /\ (x2 (@_mk_tybit1 a0 y1))) y0.
Definition term12 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type6 a0) := and (x0 (x1 x2)).
Definition term11 (a0 : Type') (x0 : type1351 a0) (x1 : type6 a0) := x0 (@_103802 a0 x1).
