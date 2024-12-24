Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : nadd) := hreal_mul (mk_hreal (nadd_eq x0)).
Definition term35 (x0 : nadd) (x1 : nadd) := fun y0 : hreal => (fun y1 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y1))) y0.
Definition term12 (x0 : nadd) (x1 : nadd) (x2 : nadd) := hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x2))).
Definition term17 (x0 : nadd) (x1 : nadd) := hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))).
Definition term22 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0)))) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq y0)))).
Definition term55 := forall y0 : nadd, forall y1 : hreal, forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq y0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq y0)) y1) (hreal_mul (mk_hreal (nadd_eq y0)) y2)).
Definition term54 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_add y1 y2)) (nadd_add (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term40 (x0 : nadd) := forall y0 : nadd, forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add (mk_hreal (nadd_eq y0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) (hreal_mul (mk_hreal (nadd_eq x0)) y1)).
Definition term39 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_add y0 y1)) (nadd_add (nadd_mul x0 y0) (nadd_mul x0 y1)).
Definition term7 (x0 : nadd) (x1 : nadd) := hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term20 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0)))) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq y0)))).
Definition term5 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term10 (x0 : nadd) (x1 : nadd) := hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term3 (x0 : nadd) (x1 : nadd) (x2 : nadd) := mk_hreal (nadd_eq (nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2))).
Definition term26 (x0 : nadd) (x1 : nadd) := forall y0 : hreal, (fun y1 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y1))) y0.
Definition term25 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (fun y1 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y1))) (mk_hreal (nadd_eq y0)).
Definition term56 := forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, (hreal_mul y1 (hreal_add y2 y3)) = (hreal_add (hreal_mul y1 y2) (hreal_mul y1 y3))) (mk_hreal (nadd_eq y0)).
Definition term41 (x0 : nadd) := forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y1) (hreal_mul (mk_hreal (nadd_eq x0)) y2))) (mk_hreal (nadd_eq y0)).
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : hreal) := (fun y0 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y0)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y0))) x2.
Definition term13 (x0 : nadd) (x1 : nadd) (x2 : nadd) := @eq hreal (mk_hreal (nadd_eq (nadd_mul x0 (nadd_add x1 x2)))).
Definition term65 := fun y0 : hreal => (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, (hreal_mul y1 (hreal_add y2 y3)) = (hreal_add (hreal_mul y1 y2) (hreal_mul y1 y3))) y0.
Definition term50 (x0 : nadd) := fun y0 : hreal => (fun y1 : hreal => forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y1) (hreal_mul (mk_hreal (nadd_eq x0)) y2))) y0.
Definition term9 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_add x0 x1)).
Definition term29 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y1))) (mk_hreal (nadd_eq y0)).
Definition term66 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_mul y0 (hreal_add y1 y2)) = (hreal_add (hreal_mul y0 y1) (hreal_mul y0 y2)).
Definition term64 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_mul x0 (hreal_add y0 y1)) = (hreal_add (hreal_mul x0 y0) (hreal_mul x0 y1)).
Definition term51 (x0 : nadd) := forall y0 : hreal, forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y0 y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y0) (hreal_mul (mk_hreal (nadd_eq x0)) y1)).
Definition term52 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_add y1 y2)) (nadd_add (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term62 := @eq Prop (forall y0 : nadd, forall y1 : hreal, forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq y0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq y0)) y1) (hreal_mul (mk_hreal (nadd_eq y0)) y2))).
Definition term47 (x0 : nadd) := @eq Prop (forall y0 : nadd, forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add (mk_hreal (nadd_eq y0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) (hreal_mul (mk_hreal (nadd_eq x0)) y1))).
Definition term0 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term27 (x0 : nadd) (x1 : nadd) := fun y0 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y0)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y0)).
Definition term28 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y0)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y0))) (mk_hreal (nadd_eq x2)).
Definition term14 (x0 : nadd) (x1 : nadd) (x2 : nadd) := @eq hreal (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x2)))).
Definition term31 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0)))) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq y0))))).
Definition term58 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul y0 (hreal_add y1 y2)) = (hreal_add (hreal_mul y0 y1) (hreal_mul y0 y2)).
Definition term43 (x0 : nadd) := fun y0 : hreal => forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y0 y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y0) (hreal_mul (mk_hreal (nadd_eq x0)) y1)).
Definition term44 (x0 : nadd) (x1 : nadd) := (fun y0 : hreal => forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y0 y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y0) (hreal_mul (mk_hreal (nadd_eq x0)) y1))) (mk_hreal (nadd_eq x1)).
Definition term48 (x0 : nadd) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y0 y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y0) (hreal_mul (mk_hreal (nadd_eq x0)) y1))) x1.
Definition term8 (x0 : nadd) (x1 : nadd) (x2 : nadd) := hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq (nadd_add x1 x2))).
Definition term37 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_add y0 y1)) (nadd_add (nadd_mul x0 y0) (nadd_mul x0 y1)).
Definition term1 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x1 (nadd_add x0 x2)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term2 (x0 : nadd) (x1 : nadd) (x2 : nadd) := mk_hreal (nadd_eq (nadd_mul x0 (nadd_add x1 x2))).
Definition term19 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_eq (nadd_mul x1 (nadd_add x0 y0)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 y0)).
Definition term18 (x0 : nadd) (x1 : nadd) (x2 : nadd) := hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x2))).
Definition term49 (x0 : hreal) (x1 : nadd) := forall y0 : hreal, (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add x0 y0)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) x0) (hreal_mul (mk_hreal (nadd_eq x1)) y0)).
Definition term36 (x0 : nadd) (x1 : nadd) := forall y0 : hreal, (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y0)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y0)).
Definition term16 (x0 : nadd) (x1 : nadd) := hreal_add (mk_hreal (nadd_eq (nadd_mul x0 x1))).
Definition term38 (x0 : nadd) := fun y0 : nadd => forall y1 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add (mk_hreal (nadd_eq y0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))) (hreal_mul (mk_hreal (nadd_eq x0)) y1)).
Definition term4 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_mul x0 (nadd_add x1 x2).
Definition term59 (x0 : nadd) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul y0 (hreal_add y1 y2)) = (hreal_add (hreal_mul y0 y1) (hreal_mul y0 y2))) (mk_hreal (nadd_eq x0)).
Definition term24 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term23 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : hreal) := hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) x2).
Definition term57 := forall y0 : hreal, (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, (hreal_mul y1 (hreal_add y2 y3)) = (hreal_add (hreal_mul y1 y2) (hreal_mul y1 y3))) y0.
Definition term42 (x0 : nadd) := forall y0 : hreal, (fun y1 : hreal => forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y1) (hreal_mul (mk_hreal (nadd_eq x0)) y2))) y0.
Definition term21 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x1 (nadd_add x0 y0)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 y0)).
Definition term53 := fun y0 : nadd => forall y1 : hreal, forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq y0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq y0)) y1) (hreal_mul (mk_hreal (nadd_eq y0)) y2)).
Definition term6 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_mul x0 x1)).
Definition term60 := fun y0 : nadd => (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, (hreal_mul y1 (hreal_add y2 y3)) = (hreal_add (hreal_mul y1 y2) (hreal_mul y1 y3))) (mk_hreal (nadd_eq y0)).
Definition term45 (x0 : nadd) := fun y0 : nadd => (fun y1 : hreal => forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y1) (hreal_mul (mk_hreal (nadd_eq x0)) y2))) (mk_hreal (nadd_eq y0)).
Definition term15 (x0 : nadd) (x1 : nadd) (x2 : nadd) := hreal_add (mk_hreal (nadd_eq (nadd_mul x1 x0))) (mk_hreal (nadd_eq (nadd_mul x1 x2))).
Definition term63 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul y0 (hreal_add y1 y2)) = (hreal_add (hreal_mul y0 y1) (hreal_mul y0 y2))) x0.
Definition term61 := @eq Prop (forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, forall y3 : hreal, (hreal_mul y1 (hreal_add y2 y3)) = (hreal_add (hreal_mul y1 y2) (hreal_mul y1 y3))) (mk_hreal (nadd_eq y0))).
Definition term46 (x0 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => forall y2 : hreal, (hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add y1 y2)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x0)) y1) (hreal_mul (mk_hreal (nadd_eq x0)) y2))) (mk_hreal (nadd_eq y0))).
Definition term30 (x0 : nadd) (x1 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => (hreal_mul (mk_hreal (nadd_eq x1)) (hreal_add (mk_hreal (nadd_eq x0)) y1)) = (hreal_add (hreal_mul (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) (hreal_mul (mk_hreal (nadd_eq x1)) y1))) (mk_hreal (nadd_eq y0))).
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : hreal) := hreal_mul (mk_hreal (nadd_eq x0)) (hreal_add (mk_hreal (nadd_eq x1)) x2).
