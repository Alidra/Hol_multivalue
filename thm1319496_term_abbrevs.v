Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 := fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) \/ (hreal_le y1 y0).
Definition term7 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) \/ (nadd_le y0 x0).
Definition term22 := fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) \/ (nadd_le y1 y0).
Definition term25 := forall y0 : nadd, forall y1 : hreal, (hreal_le (mk_hreal (nadd_eq y0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq y0))).
Definition term24 := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) \/ (nadd_le y1 y0).
Definition term3 (x0 : nadd) (x1 : nadd) := (nadd_le x1 x0) \/ (nadd_le x0 x1).
Definition term12 (x0 : nadd) := forall y0 : hreal, (fun y1 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq x0)))) y0.
Definition term6 (x0 : nadd) := fun y0 : nadd => (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) \/ (hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq x0))).
Definition term11 (x0 : nadd) := forall y0 : nadd, (fun y1 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq x0)))) (mk_hreal (nadd_eq y0)).
Definition term21 (x0 : nadd) := forall y0 : hreal, (hreal_le (mk_hreal (nadd_eq x0)) y0) \/ (hreal_le y0 (mk_hreal (nadd_eq x0))).
Definition term20 (x0 : nadd) := fun y0 : hreal => (fun y1 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq x0)))) y0.
Definition term26 := forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, (hreal_le y1 y2) \/ (hreal_le y2 y1)) (mk_hreal (nadd_eq y0)).
Definition term13 (x0 : nadd) := fun y0 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y0) \/ (hreal_le y0 (mk_hreal (nadd_eq x0))).
Definition term35 := fun y0 : hreal => (fun y1 : hreal => forall y2 : hreal, (hreal_le y1 y2) \/ (hreal_le y2 y1)) y0.
Definition term0 (x0 : nadd) (x1 : nadd) := hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term4 (x0 : nadd) (x1 : nadd) := (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) \/ (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))).
Definition term15 (x0 : nadd) := fun y0 : nadd => (fun y1 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq x0)))) (mk_hreal (nadd_eq y0)).
Definition term36 := forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) \/ (hreal_le y1 y0).
Definition term32 := @eq Prop (forall y0 : nadd, forall y1 : hreal, (hreal_le (mk_hreal (nadd_eq y0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq y0)))).
Definition term17 (x0 : nadd) := @eq Prop (forall y0 : nadd, (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) \/ (hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq x0)))).
Definition term5 (x0 : nadd) := fun y0 : nadd => (nadd_le x0 y0) \/ (nadd_le y0 x0).
Definition term2 (x0 : nadd) (x1 : nadd) := or (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))).
Definition term33 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) \/ (hreal_le y1 y0)) x0.
Definition term8 (x0 : nadd) := forall y0 : nadd, (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) \/ (hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq x0))).
Definition term34 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) \/ (hreal_le y0 x0).
Definition term23 := fun y0 : nadd => forall y1 : hreal, (hreal_le (mk_hreal (nadd_eq y0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq y0))).
Definition term18 (x0 : nadd) (x1 : hreal) := (fun y0 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y0) \/ (hreal_le y0 (mk_hreal (nadd_eq x0)))) x1.
Definition term29 (x0 : nadd) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) \/ (hreal_le y1 y0)) (mk_hreal (nadd_eq x0)).
Definition term10 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term9 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term14 (x0 : nadd) (x1 : nadd) := (fun y0 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y0) \/ (hreal_le y0 (mk_hreal (nadd_eq x0)))) (mk_hreal (nadd_eq x1)).
Definition term19 (x0 : hreal) (x1 : nadd) := (hreal_le (mk_hreal (nadd_eq x1)) x0) \/ (hreal_le x0 (mk_hreal (nadd_eq x1))).
Definition term27 := forall y0 : hreal, (fun y1 : hreal => forall y2 : hreal, (hreal_le y1 y2) \/ (hreal_le y2 y1)) y0.
Definition term1 (x0 : nadd) (x1 : nadd) := or (nadd_le x0 x1).
Definition term30 := fun y0 : nadd => (fun y1 : hreal => forall y2 : hreal, (hreal_le y1 y2) \/ (hreal_le y2 y1)) (mk_hreal (nadd_eq y0)).
Definition term31 := @eq Prop (forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, (hreal_le y1 y2) \/ (hreal_le y2 y1)) (mk_hreal (nadd_eq y0))).
Definition term16 (x0 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => (hreal_le (mk_hreal (nadd_eq x0)) y1) \/ (hreal_le y1 (mk_hreal (nadd_eq x0)))) (mk_hreal (nadd_eq y0))).
