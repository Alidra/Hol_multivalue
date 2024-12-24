Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term31 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x0) /\ (treal_eq x1 y0).
Definition term25 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y0 y1)) -> treal_eq x0 y1.
Definition term5 (x0 : prod hreal hreal) := dest_real (mk_real (treal_eq x0)).
Definition term12 (x0 : prod hreal hreal) := (fun y0 : type1233 => (real_neg (mk_real (treal_eq x0))) = (mk_real (fun y1 : prod hreal hreal => exists y2 : prod hreal hreal, (treal_eq (treal_neg y2) y1) /\ (y0 y2)))) (treal_eq x0).
Definition term36 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((treal_eq (treal_neg x1) x0) /\ (treal_eq x1 x1)) -> exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x0) /\ (treal_eq x1 y0).
Definition term22 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_eq (treal_neg x0) (treal_neg x1).
Definition term38 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x1) /\ (treal_eq x0 y0)) -> treal_eq (treal_neg x0) x1.
Definition term21 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (treal_eq x0 x1) -> treal_eq (treal_neg x0) (treal_neg x1).
Definition term26 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_eq x0 y0) /\ (treal_eq y0 y1)) -> treal_eq x0 y1) x1.
Definition term39 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x0) /\ (treal_eq x1 y0)) -> treal_eq (treal_neg x1) x0) /\ ((treal_eq (treal_neg x1) x0) -> exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x0) /\ (treal_eq x1 y0)).
Definition term37 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (treal_eq (treal_neg x1) x0) -> exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x0) /\ (treal_eq x1 y0).
Definition term7 (x0 : prod hreal hreal) := real_neg (mk_real (treal_eq x0)).
Definition term45 (x0 : prod hreal hreal) := mk_real (treal_eq (treal_neg x0)).
Definition term23 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (treal_eq (treal_neg x0) (treal_neg x1)) /\ (treal_eq (treal_neg x1) x2).
Definition term0 := fun y0 : real => mk_real (fun y1 : prod hreal hreal => exists y2 : prod hreal hreal, (treal_eq (treal_neg y2) y1) /\ (dest_real y0 y2)).
Definition term6 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_eq x0) = (treal_eq y0).
Definition term3 (x0 : real) := @eq real (real_neg x0).
Definition term41 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => treal_eq (treal_neg x0) y0.
Definition term35 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((treal_eq (treal_neg x0) x1) /\ (treal_eq x2 x0)) -> exists y0 : prod hreal hreal, (treal_eq (treal_neg y0) x1) /\ (treal_eq x2 y0).
Definition term34 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (treal_eq (treal_neg x1) x0) /\ (treal_eq x1 x1).
Definition term15 (x0 : prod hreal hreal) := @eq Prop ((real_neg (mk_real (treal_eq x0))) = (mk_real (fun y0 : prod hreal hreal => exists y1 : prod hreal hreal, (treal_eq (treal_neg y1) y0) /\ (dest_real (mk_real (treal_eq x0)) y1)))).
Definition term19 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_eq x0 y0) -> treal_eq (treal_neg x0) (treal_neg y0).
Definition term11 (x0 : prod hreal hreal) := (fun y0 : type1233 => (real_neg (mk_real (treal_eq x0))) = (mk_real (fun y1 : prod hreal hreal => exists y2 : prod hreal hreal, (treal_eq (treal_neg y2) y1) /\ (y0 y2)))) (dest_real (mk_real (treal_eq x0))).
Definition term14 (x0 : prod hreal hreal) := @eq Prop ((fun y0 : type1233 => (real_neg (mk_real (treal_eq x0))) = (mk_real (fun y1 : prod hreal hreal => exists y2 : prod hreal hreal, (treal_eq (treal_neg y2) y1) /\ (y0 y2)))) (dest_real (mk_real (treal_eq x0)))).
Definition term33 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => treal_eq y0 y0) x0.
Definition term32 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_eq (treal_neg y0) x0) /\ (treal_eq x1 y0).
Definition term18 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq y0 y1) -> treal_eq (treal_neg y0) (treal_neg y1)) x0.
Definition term28 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => ((treal_eq x1 x0) /\ (treal_eq x0 y0)) -> treal_eq x1 y0) x2.
Definition term9 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term17 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_eq (treal_neg x0) x1.
Definition term27 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : prod hreal hreal, ((treal_eq x1 x0) /\ (treal_eq x0 y0)) -> treal_eq x1 y0.
Definition term44 (x0 : prod hreal hreal) := treal_eq (treal_neg x0).
Definition term10 (x0 : prod hreal hreal) := fun y0 : type1233 => (real_neg (mk_real (treal_eq x0))) = (mk_real (fun y1 : prod hreal hreal => exists y2 : prod hreal hreal, (treal_eq (treal_neg y2) y1) /\ (y0 y2))).
Definition term42 (x0 : prod hreal hreal) := mk_real (fun y0 : prod hreal hreal => treal_eq (treal_neg x0) y0).
Definition term20 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq x0 y0) -> treal_eq (treal_neg x0) (treal_neg y0)) x1.
Definition term1 (x0 : real) := (fun y0 : real => mk_real (fun y1 : prod hreal hreal => exists y2 : prod hreal hreal, (treal_eq (treal_neg y2) y1) /\ (dest_real y0 y2))) x0.
Definition term40 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => exists y1 : prod hreal hreal, (treal_eq (treal_neg y1) y0) /\ (treal_eq x0 y1).
Definition term13 (x0 : prod hreal hreal) := mk_real (fun y0 : prod hreal hreal => exists y1 : prod hreal hreal, (treal_eq (treal_neg y1) y0) /\ (treal_eq x0 y1)).
Definition term8 (x0 : prod hreal hreal) := mk_real (fun y0 : prod hreal hreal => exists y1 : prod hreal hreal, (treal_eq (treal_neg y1) y0) /\ (dest_real (mk_real (treal_eq x0)) y1)).
Definition term2 (x0 : real) := mk_real (fun y0 : prod hreal hreal => exists y1 : prod hreal hreal, (treal_eq (treal_neg y1) y0) /\ (dest_real x0 y1)).
Definition term29 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((treal_eq x1 x0) /\ (treal_eq x0 x2)) -> treal_eq x1 x2.
Definition term46 (x0 : prod hreal hreal) := @eq real (real_neg (mk_real (treal_eq x0))).
Definition term16 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := (treal_eq (treal_neg x2) x0) /\ (treal_eq x1 x2).
Definition term43 (x0 : type1233) := fun y0 : prod hreal hreal => x0 y0.
Definition term24 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, forall y2 : prod hreal hreal, ((treal_eq y0 y1) /\ (treal_eq y1 y2)) -> treal_eq y0 y2) x0.
Definition term4 (x0 : prod hreal hreal) := exists y0 : prod hreal hreal, (treal_eq x0) = (treal_eq y0).
Definition term30 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) := ((treal_eq (treal_neg x1) (treal_neg x0)) /\ (treal_eq (treal_neg x0) x2)) -> treal_eq (treal_neg x1) x2.
