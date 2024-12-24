Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 := hreal_of_num (NUMERAL 0).
Definition term26 := fun y0 : nadd => (fun y1 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y1) = y1) (mk_hreal (nadd_eq y0)).
Definition term17 := fun y0 : nadd => (hreal_add (hreal_of_num (NUMERAL 0)) (mk_hreal (nadd_eq y0))) = (mk_hreal (nadd_eq y0)).
Definition term9 := mk_hreal (nadd_eq (nadd_of_num (NUMERAL 0))).
Definition term32 := forall y0 : hreal, (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term29 (x0 : hreal) := (fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term22 := forall y0 : nadd, (fun y1 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y1) = y1) (mk_hreal (nadd_eq y0)).
Definition term19 := forall y0 : nadd, (hreal_add (hreal_of_num (NUMERAL 0)) (mk_hreal (nadd_eq y0))) = (mk_hreal (nadd_eq y0)).
Definition term14 (x0 : nadd) := @eq hreal (mk_hreal (nadd_eq (nadd_add (nadd_of_num (NUMERAL 0)) x0))).
Definition term5 (x0 : nadd) (x1 : nadd) := hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term2 (x0 : nadd) := mk_hreal (nadd_eq (nadd_add (nadd_of_num (NUMERAL 0)) x0)).
Definition term13 (x0 : nadd) := hreal_add (hreal_of_num (NUMERAL 0)) (mk_hreal (nadd_eq x0)).
Definition term30 (x0 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) x0.
Definition term18 := forall y0 : nadd, nadd_eq (nadd_add (nadd_of_num (NUMERAL 0)) y0) y0.
Definition term7 := nadd_of_num (NUMERAL 0).
Definition term25 (x0 : nadd) := (fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0) (mk_hreal (nadd_eq x0)).
Definition term8 (x0 : nat) := mk_hreal (nadd_eq (nadd_of_num x0)).
Definition term4 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_add x0 x1)).
Definition term0 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term28 := @eq Prop (forall y0 : nadd, (hreal_add (hreal_of_num (NUMERAL 0)) (mk_hreal (nadd_eq y0))) = (mk_hreal (nadd_eq y0))).
Definition term12 := hreal_add (hreal_of_num (NUMERAL 0)).
Definition term31 := fun y0 : hreal => (fun y1 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y1) = y1) y0.
Definition term23 := forall y0 : hreal, (fun y1 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y1) = y1) y0.
Definition term6 (x0 : nadd) := hreal_add (mk_hreal (nadd_eq (nadd_of_num (NUMERAL 0)))) (mk_hreal (nadd_eq x0)).
Definition term3 (x0 : nadd) := nadd_add (nadd_of_num (NUMERAL 0)) x0.
Definition term21 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term20 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term24 := fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0.
Definition term11 := hreal_add (mk_hreal (nadd_eq (nadd_of_num (NUMERAL 0)))).
Definition term1 (x0 : nadd) := nadd_eq (nadd_add (nadd_of_num (NUMERAL 0)) x0) x0.
Definition term15 (x0 : nadd) := @eq hreal (hreal_add (hreal_of_num (NUMERAL 0)) (mk_hreal (nadd_eq x0))).
Definition term16 := fun y0 : nadd => nadd_eq (nadd_add (nadd_of_num (NUMERAL 0)) y0) y0.
Definition term27 := @eq Prop (forall y0 : nadd, (fun y1 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y1) = y1) (mk_hreal (nadd_eq y0))).
