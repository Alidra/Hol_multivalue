Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nadd) (x1 : nadd) := @eq hreal (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))).
Definition term33 (x0 : nadd) := fun y0 : hreal => forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y0) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> y0 = y1.
Definition term7 (x0 : nadd) (x1 : nadd) (x2 : nadd) := imp ((hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x2)))).
Definition term24 (x0 : nadd) (x1 : nadd) (x2 : hreal) := ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) x2)) -> (mk_hreal (nadd_eq x1)) = x2.
Definition term27 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (nadd_eq (nadd_add x0 y0) (nadd_add x0 y1)) -> nadd_eq y0 y1.
Definition term45 := forall y0 : nadd, forall y1 : hreal, forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq y0)) y1) = (hreal_add (mk_hreal (nadd_eq y0)) y2)) -> y1 = y2.
Definition term44 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq (nadd_add y0 y1) (nadd_add y0 y2)) -> nadd_eq y1 y2.
Definition term30 (x0 : nadd) := forall y0 : nadd, forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq y0)) = y1.
Definition term29 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_eq (nadd_add x0 y0) (nadd_add x0 y1)) -> nadd_eq y0 y1.
Definition term3 (x0 : nadd) (x1 : nadd) := hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term17 (x0 : nadd) (x1 : nadd) := forall y0 : hreal, (fun y1 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq x1)) = y1) y0.
Definition term16 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (fun y1 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq x1)) = y1) (mk_hreal (nadd_eq y0)).
Definition term46 := forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, ((hreal_add y1 y2) = (hreal_add y1 y3)) -> y2 = y3) (mk_hreal (nadd_eq y0)).
Definition term31 (x0 : nadd) := forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y1) = (hreal_add (mk_hreal (nadd_eq x0)) y2)) -> y1 = y2) (mk_hreal (nadd_eq y0)).
Definition term19 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y0)) -> (mk_hreal (nadd_eq x1)) = y0) (mk_hreal (nadd_eq x2)).
Definition term28 (x0 : nadd) := fun y0 : nadd => forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq y0)) = y1.
Definition term55 := fun y0 : hreal => (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, ((hreal_add y1 y2) = (hreal_add y1 y3)) -> y2 = y3) y0.
Definition term40 (x0 : nadd) := fun y0 : hreal => (fun y1 : hreal => forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y1) = (hreal_add (mk_hreal (nadd_eq x0)) y2)) -> y1 = y2) y0.
Definition term2 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_add x0 x1)).
Definition term56 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) -> y1 = y2.
Definition term54 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_add x0 y0) = (hreal_add x0 y1)) -> y0 = y1.
Definition term41 (x0 : nadd) := forall y0 : hreal, forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y0) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> y0 = y1.
Definition term42 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_eq (nadd_add y0 y1) (nadd_add y0 y2)) -> nadd_eq y1 y2.
Definition term52 := @eq Prop (forall y0 : nadd, forall y1 : hreal, forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq y0)) y1) = (hreal_add (mk_hreal (nadd_eq y0)) y2)) -> y1 = y2).
Definition term37 (x0 : nadd) := @eq Prop (forall y0 : nadd, forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq y0)) = y1).
Definition term0 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term22 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0)))) -> (mk_hreal (nadd_eq x1)) = (mk_hreal (nadd_eq y0))).
Definition term48 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) -> y1 = y2.
Definition term4 (x0 : nadd) (x1 : nadd) := @eq hreal (mk_hreal (nadd_eq (nadd_add x0 x1))).
Definition term8 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_add x0 x1) (nadd_add x0 x2)) -> nadd_eq x1 x2.
Definition term34 (x0 : nadd) (x1 : nadd) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y0) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> y0 = y1) (mk_hreal (nadd_eq x1)).
Definition term18 (x0 : nadd) (x1 : nadd) := fun y0 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y0)) -> (mk_hreal (nadd_eq x1)) = y0.
Definition term39 (x0 : nadd) (x1 : hreal) := forall y0 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) x1) = (hreal_add (mk_hreal (nadd_eq x0)) y0)) -> x1 = y0.
Definition term38 (x0 : nadd) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y0) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> y0 = y1) x1.
Definition term6 (x0 : nadd) (x1 : nadd) (x2 : nadd) := imp (nadd_eq (nadd_add x1 x0) (nadd_add x1 x2)).
Definition term11 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0)))) -> (mk_hreal (nadd_eq x1)) = (mk_hreal (nadd_eq y0)).
Definition term12 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_eq (nadd_add x0 x1) (nadd_add x0 y0)) -> nadd_eq x1 y0.
Definition term1 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_add x1 x0) (nadd_add x1 x2).
Definition term10 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_eq (nadd_add x0 x1) (nadd_add x0 y0)) -> nadd_eq x1 y0.
Definition term49 (x0 : nadd) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) -> y1 = y2) (mk_hreal (nadd_eq x0)).
Definition term25 (x0 : nadd) (x1 : nadd) := fun y0 : hreal => (fun y1 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq x1)) = y1) y0.
Definition term15 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term23 (x0 : nadd) (x1 : nadd) (x2 : hreal) := (fun y0 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y0)) -> (mk_hreal (nadd_eq x1)) = y0) x2.
Definition term26 (x0 : nadd) (x1 : nadd) := forall y0 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y0)) -> (mk_hreal (nadd_eq x1)) = y0.
Definition term14 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term47 := forall y0 : hreal, (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, ((hreal_add y1 y2) = (hreal_add y1 y3)) -> y2 = y3) y0.
Definition term32 (x0 : nadd) := forall y0 : hreal, (fun y1 : hreal => forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y1) = (hreal_add (mk_hreal (nadd_eq x0)) y2)) -> y1 = y2) y0.
Definition term13 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0)))) -> (mk_hreal (nadd_eq x1)) = (mk_hreal (nadd_eq y0)).
Definition term43 := fun y0 : nadd => forall y1 : hreal, forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq y0)) y1) = (hreal_add (mk_hreal (nadd_eq y0)) y2)) -> y1 = y2.
Definition term20 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq x1)) = y1) (mk_hreal (nadd_eq y0)).
Definition term50 := fun y0 : nadd => (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, ((hreal_add y1 y2) = (hreal_add y1 y3)) -> y2 = y3) (mk_hreal (nadd_eq y0)).
Definition term35 (x0 : nadd) := fun y0 : nadd => (fun y1 : hreal => forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y1) = (hreal_add (mk_hreal (nadd_eq x0)) y2)) -> y1 = y2) (mk_hreal (nadd_eq y0)).
Definition term9 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x2)))) -> (mk_hreal (nadd_eq x1)) = (mk_hreal (nadd_eq x2)).
Definition term53 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_add y0 y1) = (hreal_add y0 y2)) -> y1 = y2) x0.
Definition term51 := @eq Prop (forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, ((hreal_add y1 y2) = (hreal_add y1 y3)) -> y2 = y3) (mk_hreal (nadd_eq y0))).
Definition term36 (x0 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, ((hreal_add (mk_hreal (nadd_eq x0)) y1) = (hreal_add (mk_hreal (nadd_eq x0)) y2)) -> y1 = y2) (mk_hreal (nadd_eq y0))).
Definition term21 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => ((hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (hreal_add (mk_hreal (nadd_eq x0)) y1)) -> (mk_hreal (nadd_eq x1)) = y1) (mk_hreal (nadd_eq y0))).
