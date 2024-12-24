Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 := forall y0 : prod hreal hreal, (fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) (mk_real (treal_eq y0)).
Definition term1 (x0 : prod hreal hreal) := treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) x0) x0.
Definition term19 := forall y0 : prod hreal hreal, treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0.
Definition term25 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term16 (x0 : prod hreal hreal) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (mk_real (treal_eq x0))).
Definition term12 := real_mul (mk_real (treal_eq (treal_of_num (NUMERAL (BIT1 0))))).
Definition term26 (x0 : prod hreal hreal) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) (mk_real (treal_eq x0)).
Definition term15 (x0 : prod hreal hreal) := @eq real (mk_real (treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) x0))).
Definition term20 := forall y0 : prod hreal hreal, (real_mul (real_of_num (NUMERAL (BIT1 0))) (mk_real (treal_eq y0))) = (mk_real (treal_eq y0)).
Definition term18 := fun y0 : prod hreal hreal => (real_mul (real_of_num (NUMERAL (BIT1 0))) (mk_real (treal_eq y0))) = (mk_real (treal_eq y0)).
Definition term24 := forall y0 : real, (fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) y0.
Definition term32 := fun y0 : real => (fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) y0.
Definition term28 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) (mk_real (treal_eq y0))).
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term17 := fun y0 : prod hreal hreal => treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) y0) y0.
Definition term30 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term22 (x0 : real -> Prop) := forall y0 : real, x0 y0.
Definition term31 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term33 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term21 (x0 : real -> Prop) := forall y0 : prod hreal hreal, x0 (mk_real (treal_eq y0)).
Definition term8 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term13 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term27 := fun y0 : prod hreal hreal => (fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) (mk_real (treal_eq y0)).
Definition term2 (x0 : prod hreal hreal) := mk_real (treal_eq (treal_mul (treal_of_num (NUMERAL (BIT1 0))) x0)).
Definition term14 (x0 : prod hreal hreal) := real_mul (real_of_num (NUMERAL (BIT1 0))) (mk_real (treal_eq x0)).
Definition term10 := real_of_num (NUMERAL (BIT1 0)).
Definition term7 := treal_of_num (NUMERAL (BIT1 0)).
Definition term6 (x0 : prod hreal hreal) := real_mul (mk_real (treal_eq (treal_of_num (NUMERAL (BIT1 0))))) (mk_real (treal_eq x0)).
Definition term3 (x0 : prod hreal hreal) := treal_mul (treal_of_num (NUMERAL (BIT1 0))) x0.
Definition term29 := @eq Prop (forall y0 : prod hreal hreal, (real_mul (real_of_num (NUMERAL (BIT1 0))) (mk_real (treal_eq y0))) = (mk_real (treal_eq y0))).
Definition term9 := mk_real (treal_eq (treal_of_num (NUMERAL (BIT1 0)))).
Definition term11 := NUMERAL (BIT1 0).
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (treal_mul x0 x1)).
