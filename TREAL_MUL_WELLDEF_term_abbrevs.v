Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term40 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq x0 x1) /\ (treal_eq y0 y1)) -> treal_eq (treal_mul x0 y0) (treal_mul x1 y1).
Definition term26 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (exists y2 : prod hreal hreal, (treal_eq y0 y2) /\ (treal_eq y2 y1)) -> treal_eq y0 y1.
Definition term15 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y0 y1)) -> treal_eq x0 y1.
Definition term2 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_eq x0 y0) -> treal_eq (treal_mul x0 y1) (treal_mul y0 y1).
Definition term27 := (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2) -> forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (exists y2 : prod hreal hreal, (treal_eq y0 y2) /\ (treal_eq y2 y1)) -> treal_eq y0 y1.
Definition term9 := (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_eq y0 y1) -> treal_eq (treal_mul y0 y2) (treal_mul y1 y2)) -> forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_eq y0 y1) -> treal_eq (treal_mul y0 y2) (treal_mul y1 y2).
Definition term34 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := (treal_eq (treal_mul x1 x0) (treal_mul x1 x3)) /\ (treal_eq (treal_mul x1 x3) (treal_mul x2 x3)).
Definition term38 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := ((treal_eq x0 x2) /\ (treal_eq x1 x3)) -> treal_eq (treal_mul x0 x1) (treal_mul x2 x3).
Definition term11 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_mul x0 y0) = (treal_mul y0 x0).
Definition term16 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y0 y1)) -> treal_eq x0 y1) x1.
Definition term3 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq x0 y0) -> treal_eq (treal_mul x0 y1) (treal_mul y0 y1)) x1.
Definition term32 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_eq (treal_mul x0 x1).
Definition term22 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := exists y0 : prod hreal hreal, (treal_eq x0 y0) /\ (treal_eq y0 x1).
Definition term36 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_eq (treal_mul x0 x1) y0) /\ (treal_eq y0 (treal_mul x2 x3)).
Definition term39 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := forall y0 : prod hreal hreal, ((treal_eq x0 x2) /\ (treal_eq x1 y0)) -> treal_eq (treal_mul x0 x1) (treal_mul x2 y0).
Definition term30 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := (treal_eq x0 x1) /\ (treal_eq x2 x3).
Definition term7 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := treal_eq (treal_mul x0 x2) (treal_mul x1 x2).
Definition term37 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := treal_eq (treal_mul x0 x1) (treal_mul x2 x3).
Definition term29 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (exists y1 : prod hreal hreal, (treal_eq x0 y1) /\ (treal_eq y1 y0)) -> treal_eq x0 y0) x1.
Definition term6 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (treal_eq x0 x1) -> treal_eq (treal_mul x0 x2) (treal_mul x1 x2).
Definition term42 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, forall y3 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y2 y3)) -> treal_eq (treal_mul y0 y2) (treal_mul y1 y3).
Definition term41 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y1 y2)) -> treal_eq (treal_mul x0 y1) (treal_mul y0 y2).
Definition term13 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2.
Definition term0 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_eq y0 y1) -> treal_eq (treal_mul y0 y2) (treal_mul y1 y2).
Definition term25 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (exists y1 : prod hreal hreal, (treal_eq x0 y1) /\ (treal_eq y1 y0)) -> treal_eq x0 y0.
Definition term12 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_mul x0 y0) = (treal_mul y0 x0)) x1.
Definition term33 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := treal_eq (treal_mul x1 x0) (treal_mul x1 x2).
Definition term28 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (exists y2 : prod hreal hreal, (treal_eq y0 y2) /\ (treal_eq y2 y1)) -> treal_eq y0 y1) x0.
Definition term10 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0)) x0.
Definition term23 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_eq x0 y0) /\ (treal_eq y0 x1).
Definition term18 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => ((treal_eq x1 x0) /\ (treal_eq x0 y0)) -> treal_eq x1 y0) x2.
Definition term31 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := (exists y0 : prod hreal hreal, (treal_eq (treal_mul x0 x1) y0) /\ (treal_eq y0 (treal_mul x2 x3))) -> treal_eq (treal_mul x0 x1) (treal_mul x2 x3).
Definition term17 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, ((treal_eq x1 x0) /\ (treal_eq x0 y0)) -> treal_eq x1 y0.
Definition term35 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (x3 : prod hreal hreal) := exists y0 : prod hreal hreal, (treal_eq (treal_mul x0 x1) y0) /\ (treal_eq y0 (treal_mul x2 x3)).
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq x0 x1) -> treal_eq (treal_mul x0 y0) (treal_mul x1 y0)) x2.
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_eq x0 x1) -> treal_eq (treal_mul x0 y0) (treal_mul x1 y0).
Definition term21 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2) -> treal_eq x0 x1.
Definition term19 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((treal_eq x1 x0) /\ (treal_eq x0 x2)) -> treal_eq x1 x2.
Definition term8 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_eq y0 y1) -> treal_eq (treal_mul y0 y2) (treal_mul y1 y2)) -> treal_eq (treal_mul x0 x2) (treal_mul x1 x2).
Definition term24 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (exists y0 : prod hreal hreal, (treal_eq x0 y0) /\ (treal_eq y0 x1)) -> treal_eq x0 x1.
Definition term14 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2) x0.
Definition term1 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_eq y0 y1) -> treal_eq (treal_mul y0 y2) (treal_mul y1 y2)) x0.
Definition term20 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (treal_eq x0 x1) /\ (treal_eq x1 x2).
