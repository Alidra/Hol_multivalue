Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : real, (real_add (mk_real (treal_eq y0)) y1) = (real_add y1 (mk_real (treal_eq y0)))).
Definition term27 := forall y0 : prod hreal hreal, forall y1 : real, (real_add (mk_real (treal_eq y0)) y1) = (real_add y1 (mk_real (treal_eq y0))).
Definition term26 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, treal_eq (treal_add y0 y1) (treal_add y1 y0).
Definition term7 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) = (real_add (mk_real (treal_eq y0)) (mk_real (treal_eq x0))).
Definition term23 (x0 : prod hreal hreal) := forall y0 : real, (real_add (mk_real (treal_eq x0)) y0) = (real_add y0 (mk_real (treal_eq x0))).
Definition term20 (x0 : prod hreal hreal) (x1 : real) := real_add (mk_real (treal_eq x0)) x1.
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq real (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq x1))).
Definition term15 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : real => (real_add (mk_real (treal_eq x0)) y0) = (real_add y0 (mk_real (treal_eq x0)))) (mk_real (treal_eq x1)).
Definition term32 := fun y0 : prod hreal hreal => (fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) (mk_real (treal_eq y0)).
Definition term36 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term31 (x0 : prod hreal hreal) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) (mk_real (treal_eq x0)).
Definition term19 (x0 : prod hreal hreal) (x1 : real) := (fun y0 : real => (real_add (mk_real (treal_eq x0)) y0) = (real_add y0 (mk_real (treal_eq x0)))) x1.
Definition term25 := fun y0 : prod hreal hreal => forall y1 : real, (real_add (mk_real (treal_eq y0)) y1) = (real_add y1 (mk_real (treal_eq y0))).
Definition term37 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) y0.
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq real (mk_real (treal_eq (treal_add x0 x1))).
Definition term38 := forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term21 (x0 : real) (x1 : prod hreal hreal) := real_add x0 (mk_real (treal_eq x1)).
Definition term33 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) (mk_real (treal_eq y0))).
Definition term17 (x0 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => (real_add (mk_real (treal_eq x0)) y1) = (real_add y1 (mk_real (treal_eq x0)))) (mk_real (treal_eq y0))).
Definition term24 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, treal_eq (treal_add y0 y1) (treal_add y1 y0).
Definition term11 (x0 : real -> Prop) := forall y0 : real, x0 y0.
Definition term8 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, treal_eq (treal_add x0 y0) (treal_add y0 x0).
Definition term18 (x0 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) = (real_add (mk_real (treal_eq y0)) (mk_real (treal_eq x0)))).
Definition term10 (x0 : real -> Prop) := forall y0 : prod hreal hreal, x0 (mk_real (treal_eq y0)).
Definition term30 := fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term35 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term6 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => treal_eq (treal_add x0 y0) (treal_add y0 x0).
Definition term13 (x0 : prod hreal hreal) := forall y0 : real, (fun y1 : real => (real_add (mk_real (treal_eq x0)) y1) = (real_add y1 (mk_real (treal_eq x0)))) y0.
Definition term14 (x0 : prod hreal hreal) := fun y0 : real => (real_add (mk_real (treal_eq x0)) y0) = (real_add y0 (mk_real (treal_eq x0))).
Definition term0 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term29 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) y0.
Definition term28 := forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) (mk_real (treal_eq y0)).
Definition term22 (x0 : prod hreal hreal) := fun y0 : real => (fun y1 : real => (real_add (mk_real (treal_eq x0)) y1) = (real_add y1 (mk_real (treal_eq x0)))) y0.
Definition term16 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (fun y1 : real => (real_add (mk_real (treal_eq x0)) y1) = (real_add y1 (mk_real (treal_eq x0)))) (mk_real (treal_eq y0)).
Definition term3 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_add (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term12 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (fun y1 : real => (real_add (mk_real (treal_eq x0)) y1) = (real_add y1 (mk_real (treal_eq x0)))) (mk_real (treal_eq y0)).
Definition term2 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (treal_add x0 x1)).
Definition term9 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) = (real_add (mk_real (treal_eq y0)) (mk_real (treal_eq x0))).
Definition term1 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_eq (treal_add x1 x0) (treal_add x0 x1).
