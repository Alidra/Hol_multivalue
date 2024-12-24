Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term51 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq y0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq y0)) y1)).
Definition term44 := forall y0 : prod hreal hreal, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq y0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq y0)) y1).
Definition term43 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1).
Definition term16 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := imp ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x1)))).
Definition term13 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (treal_le (treal_of_num (NUMERAL 0)) x0) /\ (treal_le (treal_of_num (NUMERAL 0)) x1).
Definition term6 := real_of_num (NUMERAL 0).
Definition term22 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((treal_le (treal_of_num (NUMERAL 0)) x0) /\ (treal_le (treal_of_num (NUMERAL 0)) x1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul x0 x1).
Definition term49 := fun y0 : prod hreal hreal => (fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y1 y2)) (mk_real (treal_eq y0)).
Definition term39 (x0 : prod hreal hreal) := fun y0 : real => (fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y1)) y0.
Definition term48 (x0 : prod hreal hreal) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) (mk_real (treal_eq x0)).
Definition term7 := real_le (mk_real (treal_eq (treal_of_num (NUMERAL 0)))).
Definition term12 (x0 : prod hreal hreal) := and (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))).
Definition term11 (x0 : prod hreal hreal) := and (treal_le (treal_of_num (NUMERAL 0)) x0).
Definition term26 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) x0) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul x0 y0).
Definition term42 := fun y0 : prod hreal hreal => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq y0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq y0)) y1).
Definition term54 := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y1 y2)) y0.
Definition term55 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term17 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := treal_le (treal_of_num (NUMERAL 0)) (treal_mul x0 x1).
Definition term2 (x0 : prod hreal hreal) := real_le (mk_real (treal_eq (treal_of_num (NUMERAL 0)))) (mk_real (treal_eq x0)).
Definition term8 := real_le (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term40 (x0 : prod hreal hreal) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y0).
Definition term27 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq y0)))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq y0))).
Definition term50 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y1 y2)) (mk_real (treal_eq y0))).
Definition term35 (x0 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y1)) (mk_real (treal_eq y0))).
Definition term3 := treal_of_num (NUMERAL 0).
Definition term20 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term47 := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term32 (x0 : prod hreal hreal) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y0).
Definition term29 (x0 : real -> Prop) := forall y0 : real, x0 y0.
Definition term33 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y0)) (mk_real (treal_eq x1)).
Definition term41 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1).
Definition term36 (x0 : prod hreal hreal) := @eq Prop (forall y0 : prod hreal hreal, ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq y0)))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq y0)))).
Definition term1 (x0 : prod hreal hreal) := treal_le (treal_of_num (NUMERAL 0)) x0.
Definition term28 (x0 : real -> Prop) := forall y0 : prod hreal hreal, x0 (mk_real (treal_eq y0)).
Definition term14 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x1))).
Definition term52 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term31 (x0 : prod hreal hreal) := forall y0 : real, (fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y1)) y0.
Definition term0 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term4 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term37 (x0 : prod hreal hreal) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y0)) x1.
Definition term9 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term38 (x0 : prod hreal hreal) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) x1).
Definition term46 := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y1 y2)) y0.
Definition term45 := forall y0 : prod hreal hreal, (fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y1 y2)) (mk_real (treal_eq y0)).
Definition term34 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y1)) (mk_real (treal_eq y0)).
Definition term15 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := imp ((treal_le (treal_of_num (NUMERAL 0)) x0) /\ (treal_le (treal_of_num (NUMERAL 0)) x1)).
Definition term23 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x1)))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq x1))).
Definition term10 (x0 : prod hreal hreal) := real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0)).
Definition term30 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) y1)) (mk_real (treal_eq y0)).
Definition term24 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) x0) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul x0 y0).
Definition term21 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq x1))).
Definition term5 := mk_real (treal_eq (treal_of_num (NUMERAL 0))).
Definition term25 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => ((real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq x0))) /\ (real_le (real_of_num (NUMERAL 0)) (mk_real (treal_eq y0)))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq y0))).
Definition term18 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq (treal_of_num (NUMERAL 0)))) (mk_real (treal_eq (treal_mul x0 x1))).
Definition term19 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (treal_mul x0 x1)).
