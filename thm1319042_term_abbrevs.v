Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nadd) := hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x0)).
Definition term12 := fun y0 : nadd => (fun y1 : hreal => hreal_le y1 y1) (mk_hreal (nadd_eq y0)).
Definition term2 := fun y0 : nadd => nadd_le y0 y0.
Definition term8 := forall y0 : nadd, (fun y1 : hreal => hreal_le y1 y1) (mk_hreal (nadd_eq y0)).
Definition term17 := forall y0 : hreal, hreal_le y0 y0.
Definition term10 := fun y0 : hreal => hreal_le y0 y0.
Definition term4 := forall y0 : nadd, nadd_le y0 y0.
Definition term11 (x0 : nadd) := (fun y0 : hreal => hreal_le y0 y0) (mk_hreal (nadd_eq x0)).
Definition term0 (x0 : nadd) (x1 : nadd) := hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term15 (x0 : hreal) := (fun y0 : hreal => hreal_le y0 y0) x0.
Definition term14 := @eq Prop (forall y0 : nadd, hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq y0))).
Definition term9 := forall y0 : hreal, (fun y1 : hreal => hreal_le y1 y1) y0.
Definition term7 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term6 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term5 := forall y0 : nadd, hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq y0)).
Definition term3 := fun y0 : nadd => hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq y0)).
Definition term16 := fun y0 : hreal => (fun y1 : hreal => hreal_le y1 y1) y0.
Definition term13 := @eq Prop (forall y0 : nadd, (fun y1 : hreal => hreal_le y1 y1) (mk_hreal (nadd_eq y0))).
