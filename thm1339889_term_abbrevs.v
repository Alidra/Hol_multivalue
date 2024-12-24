Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term54 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq y0)) y1) (real_add (mk_real (treal_eq y0)) y2)).
Definition term39 (x0 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, forall y1 : real, (real_le (mk_real (treal_eq y0)) y1) -> real_le (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) (real_add (mk_real (treal_eq x0)) y1)).
Definition term32 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : real, (real_le (mk_real (treal_eq y0)) y1) -> real_le (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) (real_add (mk_real (treal_eq x0)) y1).
Definition term31 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_le y0 y1) -> treal_le (treal_add x0 y0) (treal_add x0 y1).
Definition term7 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq (treal_add x0 x1))).
Definition term20 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : real => (real_le (mk_real (treal_eq x0)) y0) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y0).
Definition term11 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x2))) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x2))).
Definition term2 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := imp (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1))).
Definition term52 := fun y0 : prod hreal hreal => (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y2 y3) -> real_le (real_add y1 y2) (real_add y1 y3)) (mk_real (treal_eq y0)).
Definition term37 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq x0)) y1) (real_add (mk_real (treal_eq x0)) y2)) (mk_real (treal_eq y0)).
Definition term27 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : real => (fun y1 : real => (real_le (mk_real (treal_eq x0)) y1) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y1)) y0.
Definition term51 (x0 : prod hreal hreal) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) (mk_real (treal_eq x0)).
Definition term30 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => forall y1 : real, (real_le (mk_real (treal_eq y0)) y1) -> real_le (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) (real_add (mk_real (treal_eq x0)) y1).
Definition term57 := fun y0 : real => (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y2 y3) -> real_le (real_add y1 y2) (real_add y1 y3)) y0.
Definition term42 (x0 : prod hreal hreal) := fun y0 : real => (fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq x0)) y1) (real_add (mk_real (treal_eq x0)) y2)) y0.
Definition term58 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term56 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1).
Definition term43 (x0 : prod hreal hreal) := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (real_add (mk_real (treal_eq x0)) y0) (real_add (mk_real (treal_eq x0)) y1).
Definition term44 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_le y1 y2) -> treal_le (treal_add y0 y1) (treal_add y0 y2).
Definition term45 := fun y0 : prod hreal hreal => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq y0)) y1) (real_add (mk_real (treal_eq y0)) y2).
Definition term9 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x2))).
Definition term36 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add (mk_real (treal_eq x0)) y0) (real_add (mk_real (treal_eq x0)) y1)) (mk_real (treal_eq x1)).
Definition term21 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (fun y0 : real => (real_le (mk_real (treal_eq x0)) y0) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y0)) (mk_real (treal_eq x2)).
Definition term15 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq y0))).
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := real_le (mk_real (treal_eq (treal_add x1 x0))) (mk_real (treal_eq (treal_add x1 x2))).
Definition term53 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y2 y3) -> real_le (real_add y1 y2) (real_add y1 y3)) (mk_real (treal_eq y0))).
Definition term38 (x0 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq x0)) y1) (real_add (mk_real (treal_eq x0)) y2)) (mk_real (treal_eq y0))).
Definition term23 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => (real_le (mk_real (treal_eq x0)) y1) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y1)) (mk_real (treal_eq y0))).
Definition term3 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := treal_le (treal_add x1 x0) (treal_add x1 x2).
Definition term35 (x0 : prod hreal hreal) := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add (mk_real (treal_eq x0)) y0) (real_add (mk_real (treal_eq x0)) y1).
Definition term17 (x0 : real -> Prop) := forall y0 : real, x0 y0.
Definition term47 := forall y0 : prod hreal hreal, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq y0)) y1) (real_add (mk_real (treal_eq y0)) y2).
Definition term46 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, (treal_le y1 y2) -> treal_le (treal_add y0 y1) (treal_add y0 y2).
Definition term29 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_le y0 y1) -> treal_le (treal_add x0 y0) (treal_add x0 y1).
Definition term1 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := imp (treal_le x0 x1).
Definition term24 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq y0)))).
Definition term8 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (real_add (mk_real (treal_eq x0)) (mk_real (treal_eq x1))).
Definition term25 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : real) := (fun y0 : real => (real_le (mk_real (treal_eq x0)) y0) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y0)) x2.
Definition term16 (x0 : real -> Prop) := forall y0 : prod hreal hreal, x0 (mk_real (treal_eq y0)).
Definition term19 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : real, (fun y1 : real => (real_le (mk_real (treal_eq x0)) y1) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y1)) y0.
Definition term0 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term12 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_le x0 y0) -> treal_le (treal_add x1 x0) (treal_add x1 y0).
Definition term40 (x0 : prod hreal hreal) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add (mk_real (treal_eq x0)) y0) (real_add (mk_real (treal_eq x0)) y1)) x1.
Definition term41 (x0 : real) (x1 : prod hreal hreal) := forall y0 : real, (real_le x0 y0) -> real_le (real_add (mk_real (treal_eq x1)) x0) (real_add (mk_real (treal_eq x1)) y0).
Definition term28 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : real, (real_le (mk_real (treal_eq x0)) y0) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y0).
Definition term50 := fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term49 := forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y2 y3) -> real_le (real_add y1 y2) (real_add y1 y3)) y0.
Definition term34 (x0 : prod hreal hreal) := forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq x0)) y1) (real_add (mk_real (treal_eq x0)) y2)) y0.
Definition term48 := forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y2 y3) -> real_le (real_add y1 y2) (real_add y1 y3)) (mk_real (treal_eq y0)).
Definition term33 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (real_add (mk_real (treal_eq x0)) y1) (real_add (mk_real (treal_eq x0)) y2)) (mk_real (treal_eq y0)).
Definition term14 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_le x0 y0) -> treal_le (treal_add x1 x0) (treal_add x1 y0).
Definition term10 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (treal_le x0 x2) -> treal_le (treal_add x1 x0) (treal_add x1 x2).
Definition term22 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : prod hreal hreal => (fun y1 : real => (real_le (mk_real (treal_eq x0)) y1) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y1)) (mk_real (treal_eq y0)).
Definition term6 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_add (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term26 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : real) := (real_le (mk_real (treal_eq x0)) x2) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) x2).
Definition term18 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, (fun y1 : real => (real_le (mk_real (treal_eq x0)) y1) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) y1)) (mk_real (treal_eq y0)).
Definition term13 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : prod hreal hreal => (real_le (mk_real (treal_eq x0)) (mk_real (treal_eq y0))) -> real_le (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq x0))) (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq y0))).
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (treal_add x0 x1)).
Definition term55 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) x0.
