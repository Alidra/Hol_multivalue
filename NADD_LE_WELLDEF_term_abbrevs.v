Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, exists y3 : nadd, (nadd_eq y2 y0) /\ ((nadd_eq y3 y1) /\ (nadd_le y2 y3))) -> nadd_le y0 y1) x0.
Definition term0 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0)) x0.
Definition term15 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => (nadd_eq x2 x0) /\ ((nadd_eq y0 x1) /\ (nadd_le x2 y0)).
Definition term1 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (nadd_eq y0 x0).
Definition term11 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ ((nadd_eq x1 x3) /\ (nadd_le x0 x1))) -> nadd_le x2 x3.
Definition term35 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3).
Definition term34 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2).
Definition term33 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1).
Definition term20 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, exists y3 : nadd, (nadd_eq y2 y0) /\ ((nadd_eq y3 y1) /\ (nadd_le y2 y3))) -> nadd_le y0 y1.
Definition term7 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ ((nadd_eq y0 y1) /\ (nadd_le x0 y0))) -> nadd_le x1 y1.
Definition term5 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ ((nadd_eq y1 y2) /\ (nadd_le x0 y1))) -> nadd_le y0 y2.
Definition term3 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ ((nadd_eq y2 y3) /\ (nadd_le y0 y2))) -> nadd_le y1 y3.
Definition term31 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> (nadd_le x0 x1) = (nadd_le x2 x3).
Definition term24 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term23 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, exists y2 : nadd, (nadd_eq y1 x0) /\ ((nadd_eq y2 y0) /\ (nadd_le y1 y2))) -> nadd_le x0 y0) x1.
Definition term21 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ ((nadd_eq y2 y3) /\ (nadd_le y0 y2))) -> nadd_le y1 y3) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, exists y3 : nadd, (nadd_eq y2 y0) /\ ((nadd_eq y3 y1) /\ (nadd_le y2 y3))) -> nadd_le y0 y1.
Definition term28 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x2) /\ ((nadd_eq x1 x3) /\ (nadd_le x2 x3)).
Definition term10 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => ((nadd_eq x0 x2) /\ ((nadd_eq x1 y0) /\ (nadd_le x0 x1))) -> nadd_le x2 y0) x3.
Definition term13 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ ((nadd_eq y2 y3) /\ (nadd_le y0 y2))) -> nadd_le y1 y3) -> nadd_le x0 x1.
Definition term19 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, exists y2 : nadd, (nadd_eq y1 x0) /\ ((nadd_eq y2 y0) /\ (nadd_le y1 y2))) -> nadd_le x0 y0.
Definition term6 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ ((nadd_eq y1 y2) /\ (nadd_le x0 y1))) -> nadd_le y0 y2) x1.
Definition term29 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) -> nadd_le x2 x3.
Definition term4 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ ((nadd_eq y2 y3) /\ (nadd_le y0 y2))) -> nadd_le y1 y3) x0.
Definition term25 (x0 : nadd) (x1 : nadd) := and (nadd_eq x0 x1).
Definition term8 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ ((nadd_eq y0 y1) /\ (nadd_le x0 y0))) -> nadd_le x1 y1) x2.
Definition term14 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nadd, (nadd_eq x2 x0) /\ ((nadd_eq y0 x1) /\ (nadd_le x2 y0)).
Definition term12 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3)).
Definition term30 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_le x2 x3) -> nadd_le x0 x1) /\ ((nadd_le x0 x1) -> nadd_le x2 x3).
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x2 x0) /\ (nadd_le x1 x2).
Definition term17 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => exists y1 : nadd, (nadd_eq y0 x0) /\ ((nadd_eq y1 x1) /\ (nadd_le y0 y1)).
Definition term16 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, exists y1 : nadd, (nadd_eq y0 x0) /\ ((nadd_eq y1 x1) /\ (nadd_le y0 y1)).
Definition term9 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ ((nadd_eq x1 y0) /\ (nadd_le x0 x1))) -> nadd_le x2 y0.
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0).
Definition term2 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (nadd_eq y0 x0)) x1.
Definition term27 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x0 x2) /\ (nadd_le x1 x2).
Definition term18 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, exists y1 : nadd, (nadd_eq y0 x0) /\ ((nadd_eq y1 x1) /\ (nadd_le y0 y1))) -> nadd_le x0 x1.
