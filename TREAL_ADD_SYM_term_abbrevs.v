Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, treal_eq (treal_add y0 y1) (treal_add y1 y0).
Definition term0 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1.
Definition term6 := (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1) -> forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1.
Definition term2 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (x0 = y0) -> treal_eq x0 y0.
Definition term9 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_add x0 y0) = (treal_add y0 x0).
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (x0 = x1) -> treal_eq x0 x1.
Definition term3 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (x0 = y0) -> treal_eq x0 y0) x1.
Definition term12 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, treal_eq (treal_add x0 y0) (treal_add y0 x0).
Definition term7 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((treal_add x1 x0) = (treal_add x0 x1)) -> treal_eq (treal_add x1 x0) (treal_add x0 x1).
Definition term10 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_add x0 y0) = (treal_add y0 x0)) x1.
Definition term8 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_add y0 y1) = (treal_add y1 y0)) x0.
Definition term1 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1) x0.
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1) -> treal_eq x0 x1.
Definition term11 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_eq (treal_add x1 x0) (treal_add x0 x1).
