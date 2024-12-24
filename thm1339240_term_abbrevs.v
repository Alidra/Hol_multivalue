Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := forall y0 : prod hreal hreal, treal_le y0 y0.
Definition term5 := forall y0 : prod hreal hreal, real_le (mk_real (treal_eq y0)) (mk_real (treal_eq y0)).
Definition term8 := forall y0 : prod hreal hreal, (fun y1 : real => real_le y1 y1) (mk_real (treal_eq y0)).
Definition term17 := forall y0 : real, real_le y0 y0.
Definition term9 := forall y0 : real, (fun y1 : real => real_le y1 y1) y0.
Definition term2 := fun y0 : prod hreal hreal => treal_le y0 y0.
Definition term13 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => real_le y1 y1) (mk_real (treal_eq y0))).
Definition term12 := fun y0 : prod hreal hreal => (fun y1 : real => real_le y1 y1) (mk_real (treal_eq y0)).
Definition term7 (x0 : real -> Prop) := forall y0 : real, x0 y0.
Definition term6 (x0 : real -> Prop) := forall y0 : prod hreal hreal, x0 (mk_real (treal_eq y0)).
Definition term10 := fun y0 : real => real_le y0 y0.
Definition term0 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term1 (x0 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x0)).
Definition term3 := fun y0 : prod hreal hreal => real_le (mk_real (treal_eq y0)) (mk_real (treal_eq y0)).
Definition term15 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term11 (x0 : prod hreal hreal) := (fun y0 : real => real_le y0 y0) (mk_real (treal_eq x0)).
Definition term14 := @eq Prop (forall y0 : prod hreal hreal, real_le (mk_real (treal_eq y0)) (mk_real (treal_eq y0))).
Definition term16 := fun y0 : real => (fun y1 : real => real_le y1 y1) y0.
