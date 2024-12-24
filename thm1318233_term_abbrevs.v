Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq x1 x0) /\ (nadd_eq x0 x2)) -> nadd_eq x1 x2.
Definition term18 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) -> nadd_eq (nadd_inv y0) (nadd_inv y1)) x0.
Definition term21 (x0 : nadd) (x1 : nadd) := (nadd_eq x0 x1) -> nadd_eq (nadd_inv x0) (nadd_inv x1).
Definition term36 (x0 : nadd) (x1 : nadd) := ((nadd_eq (nadd_inv x1) x0) /\ (nadd_eq x1 x1)) -> exists y0 : nadd, (nadd_eq (nadd_inv y0) x0) /\ (nadd_eq x1 y0).
Definition term25 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1.
Definition term31 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_eq (nadd_inv y0) x0) /\ (nadd_eq x1 y0).
Definition term37 (x0 : nadd) (x1 : nadd) := (nadd_eq (nadd_inv x1) x0) -> exists y0 : nadd, (nadd_eq (nadd_inv y0) x0) /\ (nadd_eq x1 y0).
Definition term39 (x0 : nadd) (x1 : nadd) := ((exists y0 : nadd, (nadd_eq (nadd_inv y0) x0) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_inv x1) x0) /\ ((nadd_eq (nadd_inv x1) x0) -> exists y0 : nadd, (nadd_eq (nadd_inv y0) x0) /\ (nadd_eq x1 y0)).
Definition term7 (x0 : nadd) := hreal_inv (mk_hreal (nadd_eq x0)).
Definition term38 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_inv y0) x1) /\ (nadd_eq x0 y0)) -> nadd_eq (nadd_inv x0) x1.
Definition term10 (x0 : nadd) := fun y0 : nadd -> Prop => (hreal_inv (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, (nadd_eq (nadd_inv y2) y1) /\ (y0 y2))).
Definition term45 (x0 : nadd) := mk_hreal (nadd_eq (nadd_inv x0)).
Definition term15 (x0 : nadd) := @eq Prop ((hreal_inv (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y0 : nadd => exists y1 : nadd, (nadd_eq (nadd_inv y1) y0) /\ (dest_hreal (mk_hreal (nadd_eq x0)) y1)))).
Definition term13 (x0 : nadd) := mk_hreal (fun y0 : nadd => exists y1 : nadd, (nadd_eq (nadd_inv y1) y0) /\ (nadd_eq x0 y1)).
Definition term8 (x0 : nadd) := mk_hreal (fun y0 : nadd => exists y1 : nadd, (nadd_eq (nadd_inv y1) y0) /\ (dest_hreal (mk_hreal (nadd_eq x0)) y1)).
Definition term2 (x0 : hreal) := mk_hreal (fun y0 : nadd => exists y1 : nadd, (nadd_eq (nadd_inv y1) y0) /\ (dest_hreal x0 y1)).
Definition term6 (x0 : nadd) := fun y0 : nadd => (nadd_eq x0) = (nadd_eq y0).
Definition term34 (x0 : nadd) (x1 : nadd) := (nadd_eq (nadd_inv x1) x0) /\ (nadd_eq x1 x1).
Definition term14 (x0 : nadd) := @eq Prop ((fun y0 : nadd -> Prop => (hreal_inv (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, (nadd_eq (nadd_inv y2) y1) /\ (y0 y2)))) (dest_hreal (mk_hreal (nadd_eq x0)))).
Definition term32 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_eq (nadd_inv y0) x0) /\ (nadd_eq x1 y0).
Definition term33 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term24 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) x0.
Definition term40 (x0 : nadd) := fun y0 : nadd => exists y1 : nadd, (nadd_eq (nadd_inv y1) y0) /\ (nadd_eq x0 y1).
Definition term9 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term30 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq (nadd_inv x1) (nadd_inv x0)) /\ (nadd_eq (nadd_inv x0) x2)) -> nadd_eq (nadd_inv x1) x2.
Definition term43 (x0 : nadd -> Prop) := fun y0 : nadd => x0 y0.
Definition term23 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_inv x0) (nadd_inv x1)) /\ (nadd_eq (nadd_inv x1) x2).
Definition term16 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_inv x2) x0) /\ (nadd_eq x1 x2).
Definition term28 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0) x2.
Definition term4 (x0 : nadd) := exists y0 : nadd, (nadd_eq x0) = (nadd_eq y0).
Definition term5 (x0 : nadd) := dest_hreal (mk_hreal (nadd_eq x0)).
Definition term0 := fun y0 : hreal => mk_hreal (fun y1 : nadd => exists y2 : nadd, (nadd_eq (nadd_inv y2) y1) /\ (dest_hreal y0 y2)).
Definition term44 (x0 : nadd) := nadd_eq (nadd_inv x0).
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq (nadd_inv x0) x1) /\ (nadd_eq x2 x0)) -> exists y0 : nadd, (nadd_eq (nadd_inv y0) x1) /\ (nadd_eq x2 y0).
Definition term11 (x0 : nadd) := (fun y0 : nadd -> Prop => (hreal_inv (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, (nadd_eq (nadd_inv y2) y1) /\ (y0 y2)))) (dest_hreal (mk_hreal (nadd_eq x0))).
Definition term20 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) -> nadd_eq (nadd_inv x0) (nadd_inv y0)) x1.
Definition term27 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0.
Definition term22 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_inv x0) (nadd_inv x1).
Definition term12 (x0 : nadd) := (fun y0 : nadd -> Prop => (hreal_inv (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, (nadd_eq (nadd_inv y2) y1) /\ (y0 y2)))) (nadd_eq x0).
Definition term26 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1) x1.
Definition term1 (x0 : hreal) := (fun y0 : hreal => mk_hreal (fun y1 : nadd => exists y2 : nadd, (nadd_eq (nadd_inv y2) y1) /\ (dest_hreal y0 y2))) x0.
Definition term17 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_inv x0) x1.
Definition term46 (x0 : nadd) := @eq hreal (hreal_inv (mk_hreal (nadd_eq x0))).
Definition term19 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) -> nadd_eq (nadd_inv x0) (nadd_inv y0).
Definition term41 (x0 : nadd) := fun y0 : nadd => nadd_eq (nadd_inv x0) y0.
Definition term3 (x0 : hreal) := @eq hreal (hreal_inv x0).
Definition term42 (x0 : nadd) := mk_hreal (fun y0 : nadd => nadd_eq (nadd_inv x0) y0).
