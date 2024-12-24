Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := (fun y0 : real => fun y1 : real => fun y2 : real => exists y3 : real, (integer y3) /\ ((real_sub y1 y2) = (real_mul y3 y0))) x0.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, (integer y0) /\ ((real_sub x0 x1) = (real_mul y0 x2)).
Definition term15 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mod y2 y0 y1) = (exists y3 : real, (integer y3) /\ ((real_sub y0 y1) = (real_mul y3 y2))).
Definition term14 (x0 : real) := forall y0 : real, forall y1 : real, (real_mod y1 x0 y0) = (exists y2 : real, (integer y2) /\ ((real_sub x0 y0) = (real_mul y2 y1))).
Definition term9 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mod y0 y1 y2) = (exists y3 : real, (integer y3) /\ ((real_sub y1 y2) = (real_mul y3 y0))).
Definition term8 (x0 : real) := forall y0 : real, forall y1 : real, (real_mod x0 y0 y1) = (exists y2 : real, (integer y2) /\ ((real_sub y0 y1) = (real_mul y2 x0))).
Definition term2 (x0 : real) := fun y0 : real => fun y1 : real => exists y2 : real, (integer y2) /\ ((real_sub y0 y1) = (real_mul y2 x0)).
Definition term13 (x0 : real) (x1 : real) := forall y0 : real, (real_mod y0 x0 x1) = (exists y1 : real, (integer y1) /\ ((real_sub x0 x1) = (real_mul y1 y0))).
Definition term7 (x0 : real) (x1 : real) := forall y0 : real, (real_mod x1 x0 y0) = (exists y1 : real, (integer y1) /\ ((real_sub x0 y0) = (real_mul y1 x1))).
Definition term12 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mod x1 x0 y0) = (exists y1 : real, (integer y1) /\ ((real_sub x0 y0) = (real_mul y1 x1)))) x2.
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => exists y1 : real, (integer y1) /\ ((real_sub x0 y0) = (real_mul y1 x1))) x2.
Definition term4 (x0 : real) (x1 : real) := fun y0 : real => exists y1 : real, (integer y1) /\ ((real_sub x0 y0) = (real_mul y1 x1)).
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mod x0 y0 y1) = (exists y2 : real, (integer y2) /\ ((real_sub y0 y1) = (real_mul y2 x0)))) x1.
Definition term0 := fun y0 : real => fun y1 : real => fun y2 : real => exists y3 : real, (integer y3) /\ ((real_sub y1 y2) = (real_mul y3 y0)).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => fun y1 : real => exists y2 : real, (integer y2) /\ ((real_sub y0 y1) = (real_mul y2 x0))) x1.
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mod y0 y1 y2) = (exists y3 : real, (integer y3) /\ ((real_sub y1 y2) = (real_mul y3 y0)))) x0.
