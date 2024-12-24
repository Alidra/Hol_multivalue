Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, treal_eq (treal_mul y0 y1) (treal_mul y1 y0).
Definition term4 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (x0 = y0) -> treal_eq x0 y0.
Definition term15 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term1 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_mul x0 y0) = (treal_mul y0 x0).
Definition term11 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => treal_eq (treal_mul x0 y0) (treal_mul y0 x0).
Definition term6 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (x0 = x1) -> treal_eq x0 x1.
Definition term10 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_eq (treal_mul x1 x0) (treal_mul x0 x1).
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (x0 = y0) -> treal_eq x0 y0) x1.
Definition term17 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, treal_eq (treal_mul y0 y1) (treal_mul y1 y0).
Definition term9 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq (prod hreal hreal) (treal_mul x0 x1).
Definition term7 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (x0 = x1) -> (treal_eq x0 x1) = True.
Definition term13 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, treal_eq (treal_mul x0 y0) (treal_mul y0 x0).
Definition term8 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((treal_mul x1 x0) = (treal_mul x0 x1)) -> (treal_eq (treal_mul x1 x0) (treal_mul x0 x1)) = True.
Definition term2 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_mul x0 y0) = (treal_mul y0 x0)) x1.
Definition term3 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1) x0.
Definition term0 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_mul y0 y1) = (treal_mul y1 y0)) x0.
Definition term14 := forall y0 : prod hreal hreal, True.
Definition term12 := fun y0 : prod hreal hreal => True.
Definition term16 (x0 : Prop) := forall y0 : prod hreal hreal, x0.
