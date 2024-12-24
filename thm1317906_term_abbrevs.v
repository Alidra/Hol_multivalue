Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y2 : nadd => exists y3 : nadd, exists y4 : nadd, (nadd_eq (nadd_add y3 y4) y2) /\ ((y0 y3) /\ (y1 y4))))) (dest_hreal (mk_hreal (nadd_eq x1))).
Definition term43 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq x1 x0) /\ (nadd_eq x0 x2)) -> nadd_eq x1 x2.
Definition term63 (x0 : nadd) (x1 : nadd) := @eq hreal (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))).
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_add x0 x1) (nadd_add x2 y0)) x3.
Definition term21 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((nadd_eq x0 y2) /\ (y0 y3))))) (nadd_eq x1).
Definition term15 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y2 : nadd => exists y3 : nadd, exists y4 : nadd, (nadd_eq (nadd_add y3 y4) y2) /\ ((y0 y3) /\ (y1 y4))))) (nadd_eq x1).
Definition term39 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1.
Definition term31 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_add x0 y0) (nadd_add x1 y1).
Definition term29 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_add x0 y1) (nadd_add y0 y2).
Definition term4 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((dest_hreal x0 y2) /\ (dest_hreal y0 y3)))) x1.
Definition term1 (x0 : hreal) := (fun y0 : hreal => fun y1 : hreal => mk_hreal (fun y2 : nadd => exists y3 : nadd, exists y4 : nadd, (nadd_eq (nadd_add y3 y4) y2) /\ ((dest_hreal y0 y3) /\ (dest_hreal y1 y4)))) x0.
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term44 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nadd) := ((nadd_eq (nadd_add x2 x3) (nadd_add x0 x1)) /\ (nadd_eq (nadd_add x0 x1) x4)) -> nadd_eq (nadd_add x2 x3) x4.
Definition term56 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1))) -> nadd_eq (nadd_add x1 x2) x0) /\ ((nadd_eq (nadd_add x1 x2) x0) -> exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1))).
Definition term10 (x0 : nadd) (x1 : nadd) := hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term17 (x0 : nadd) (x1 : nadd) := @eq ((nadd -> Prop) -> Prop) ((fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y2 : nadd => exists y3 : nadd, exists y4 : nadd, (nadd_eq (nadd_add y3 y4) y2) /\ ((y0 y3) /\ (y1 y4))))) (dest_hreal (mk_hreal (nadd_eq x1)))).
Definition term61 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_add x0 x1).
Definition term27 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_add x0 x1) x2.
Definition term36 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_add x0 x1) (nadd_add x2 x3).
Definition term22 (x0 : nadd) (x1 : nadd) := mk_hreal (fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_eq (nadd_add y1 y2) y0) /\ ((nadd_eq x0 y1) /\ (nadd_eq x1 y2))).
Definition term11 (x0 : nadd) (x1 : nadd) := mk_hreal (fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_eq (nadd_add y1 y2) y0) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y1) /\ (dest_hreal (mk_hreal (nadd_eq x1)) y2))).
Definition term5 (x0 : hreal) (x1 : hreal) := mk_hreal (fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_eq (nadd_add y1 y2) y0) /\ ((dest_hreal x0 y1) /\ (dest_hreal x1 y2))).
Definition term30 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_add x0 y1) (nadd_add y0 y2)) x1.
Definition term50 (x0 : nadd) (x1 : nadd) := (nadd_eq x0 x0) /\ (nadd_eq x1 x1).
Definition term51 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x1 x2) x0) /\ ((nadd_eq x1 x1) /\ (nadd_eq x2 x2)).
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := fun y0 : nadd => (nadd_eq (nadd_add x2 y0) x0) /\ ((nadd_eq x1 x2) /\ (nadd_eq x3 y0)).
Definition term9 (x0 : nadd) := fun y0 : nadd => (nadd_eq x0) = (nadd_eq y0).
Definition term23 (x0 : nadd) (x1 : nadd) := @eq Prop ((fun y0 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y2) /\ (y0 y3))))) (dest_hreal (mk_hreal (nadd_eq x1)))).
Definition term62 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_add x0 x1)).
Definition term49 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term38 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) x0.
Definition term28 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_add y0 y2) (nadd_add y1 y3)) x0.
Definition term59 (x0 : nadd) (x1 : nadd) := mk_hreal (fun y0 : nadd => nadd_eq (nadd_add x0 x1) y0).
Definition term12 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term55 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x2) /\ ((nadd_eq x0 y0) /\ (nadd_eq x1 y1))) -> nadd_eq (nadd_add x0 x1) x2.
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x1 x2) x0) -> exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term19 (x0 : nadd) (x1 : nadd) := @eq ((nadd -> Prop) -> Prop) (fun y0 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((dest_hreal (mk_hreal (nadd_eq x1)) y2) /\ (y0 y3))))).
Definition term25 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nadd) := (nadd_eq (nadd_add x2 x4) x0) /\ ((nadd_eq x1 x2) /\ (nadd_eq x3 x4)).
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_add x0 y0) (nadd_add x1 y1)) x2.
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> nadd_eq (nadd_add x0 x1) (nadd_add x2 x3).
Definition term20 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y2) /\ (y0 y3))))) (dest_hreal (mk_hreal (nadd_eq x1))).
Definition term60 (x0 : nadd -> Prop) := fun y0 : nadd => x0 y0.
Definition term45 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := exists y0 : nadd, (nadd_eq (nadd_add x2 y0) x0) /\ ((nadd_eq x1 x2) /\ (nadd_eq x3 y0)).
Definition term42 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0) x2.
Definition term0 := fun y0 : hreal => fun y1 : hreal => mk_hreal (fun y2 : nadd => exists y3 : nadd, exists y4 : nadd, (nadd_eq (nadd_add y3 y4) y2) /\ ((dest_hreal y0 y3) /\ (dest_hreal y1 y4))).
Definition term7 (x0 : nadd) := exists y0 : nadd, (nadd_eq x0) = (nadd_eq y0).
Definition term3 (x0 : hreal) := @eq (hreal -> hreal) (hreal_add x0).
Definition term58 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_eq (nadd_add x0 x1) y0.
Definition term48 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term8 (x0 : nadd) := dest_hreal (mk_hreal (nadd_eq x0)).
Definition term47 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term24 (x0 : nadd) (x1 : nadd) := @eq Prop ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (mk_hreal (fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_eq (nadd_add y1 y2) y0) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y1) /\ (dest_hreal (mk_hreal (nadd_eq x1)) y2))))).
Definition term2 (x0 : hreal) := fun y0 : hreal => mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((dest_hreal x0 y2) /\ (dest_hreal y0 y3))).
Definition term6 (x0 : hreal) (x1 : hreal) := @eq hreal (hreal_add x0 x1).
Definition term13 (x0 : nadd) (x1 : nadd) := fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (mk_hreal (fun y2 : nadd => exists y3 : nadd, exists y4 : nadd, (nadd_eq (nadd_add y3 y4) y2) /\ ((y0 y3) /\ (y1 y4)))).
Definition term41 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0.
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_add x0 x1) (nadd_add x2 y0).
Definition term37 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nadd) := (nadd_eq (nadd_add x0 x1) (nadd_add x2 x3)) /\ (nadd_eq (nadd_add x2 x3) x4).
Definition term40 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1) x1.
Definition term57 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_eq (nadd_add y1 y2) y0) /\ ((nadd_eq x0 y1) /\ (nadd_eq x1 y2)).
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq (nadd_add x1 x2) x0) /\ ((nadd_eq x1 x1) /\ (nadd_eq x2 x2))) -> exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nadd) := ((nadd_eq (nadd_add x0 x1) x2) /\ ((nadd_eq x3 x0) /\ (nadd_eq x4 x1))) -> exists y0 : nadd, exists y1 : nadd, (nadd_eq (nadd_add y0 y1) x2) /\ ((nadd_eq x3 y0) /\ (nadd_eq x4 y1)).
Definition term18 (x0 : nadd) (x1 : nadd) := fun y0 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((dest_hreal (mk_hreal (nadd_eq x1)) y2) /\ (y0 y3)))).
Definition term16 (x0 : nadd) (x1 : nadd) := fun y0 : nadd -> Prop => (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (mk_hreal (fun y1 : nadd => exists y2 : nadd, exists y3 : nadd, (nadd_eq (nadd_add y2 y3) y1) /\ ((nadd_eq x1 y2) /\ (y0 y3)))).
