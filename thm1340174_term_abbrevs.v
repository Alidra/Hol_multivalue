Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 := fun y0 : prod hreal hreal => (~ (treal_eq y0 (treal_of_num (NUMERAL 0)))) -> treal_eq (treal_mul (treal_inv y0) y0) (treal_of_num (NUMERAL (BIT1 0))).
Definition term46 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term28 (x0 : prod hreal hreal) := (~ (treal_eq x0 (treal_of_num (NUMERAL 0)))) -> treal_eq (treal_mul (treal_inv x0) x0) (treal_of_num (NUMERAL (BIT1 0))).
Definition term29 (x0 : prod hreal hreal) := (~ ((mk_real (treal_eq x0)) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv (mk_real (treal_eq x0))) (mk_real (treal_eq x0))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term5 := real_of_num (NUMERAL 0).
Definition term38 := fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term45 := fun y0 : real => (fun y1 : real => (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term6 (x0 : prod hreal hreal) := @eq real (mk_real (treal_eq x0)).
Definition term24 (x0 : prod hreal hreal) := @eq real (mk_real (treal_eq (treal_mul (treal_inv x0) x0))).
Definition term14 (x0 : prod hreal hreal) := treal_mul (treal_inv x0) x0.
Definition term43 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term22 (x0 : prod hreal hreal) := real_mul (real_inv (mk_real (treal_eq x0))).
Definition term44 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term41 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : real => (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y1) y1) = (real_of_num (NUMERAL (BIT1 0)))) (mk_real (treal_eq y0))).
Definition term3 := treal_of_num (NUMERAL 0).
Definition term17 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_mul (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term20 (x0 : prod hreal hreal) := real_inv (mk_real (treal_eq x0)).
Definition term23 (x0 : prod hreal hreal) := real_mul (real_inv (mk_real (treal_eq x0))) (mk_real (treal_eq x0)).
Definition term18 (x0 : prod hreal hreal) := real_mul (mk_real (treal_eq (treal_inv x0))) (mk_real (treal_eq x0)).
Definition term35 (x0 : real -> Prop) := forall y0 : real, x0 y0.
Definition term42 := @eq Prop (forall y0 : prod hreal hreal, (~ ((mk_real (treal_eq y0)) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv (mk_real (treal_eq y0))) (mk_real (treal_eq y0))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : prod hreal hreal) := mk_real (treal_eq (treal_mul (treal_inv x0) x0)).
Definition term10 (x0 : prod hreal hreal) := imp (~ ((mk_real (treal_eq x0)) = (real_of_num (NUMERAL 0)))).
Definition term34 (x0 : real -> Prop) := forall y0 : prod hreal hreal, x0 (mk_real (treal_eq y0)).
Definition term9 (x0 : prod hreal hreal) := imp (~ (treal_eq x0 (treal_of_num (NUMERAL 0)))).
Definition term37 := forall y0 : real, (fun y1 : real => (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y1) y1) = (real_of_num (NUMERAL (BIT1 0)))) y0.
Definition term4 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term19 (x0 : prod hreal hreal) := mk_real (treal_eq (treal_inv x0)).
Definition term8 (x0 : prod hreal hreal) := ~ ((mk_real (treal_eq x0)) = (real_of_num (NUMERAL 0))).
Definition term7 (x0 : prod hreal hreal) := ~ (treal_eq x0 (treal_of_num (NUMERAL 0))).
Definition term0 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term1 (x0 : prod hreal hreal) := treal_eq x0 (treal_of_num (NUMERAL 0)).
Definition term11 (x0 : prod hreal hreal) := treal_eq (treal_mul (treal_inv x0) x0) (treal_of_num (NUMERAL (BIT1 0))).
Definition term31 := fun y0 : prod hreal hreal => (~ ((mk_real (treal_eq y0)) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv (mk_real (treal_eq y0))) (mk_real (treal_eq y0))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term26 := real_of_num (NUMERAL (BIT1 0)).
Definition term15 := treal_of_num (NUMERAL (BIT1 0)).
Definition term39 (x0 : prod hreal hreal) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) (mk_real (treal_eq x0)).
Definition term21 (x0 : prod hreal hreal) := real_mul (mk_real (treal_eq (treal_inv x0))).
Definition term40 := fun y0 : prod hreal hreal => (fun y1 : real => (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y1) y1) = (real_of_num (NUMERAL (BIT1 0)))) (mk_real (treal_eq y0)).
Definition term33 := forall y0 : prod hreal hreal, (~ ((mk_real (treal_eq y0)) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv (mk_real (treal_eq y0))) (mk_real (treal_eq y0))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term32 := forall y0 : prod hreal hreal, (~ (treal_eq y0 (treal_of_num (NUMERAL 0)))) -> treal_eq (treal_mul (treal_inv y0) y0) (treal_of_num (NUMERAL (BIT1 0))).
Definition term36 := forall y0 : prod hreal hreal, (fun y1 : real => (~ (y1 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y1) y1) = (real_of_num (NUMERAL (BIT1 0)))) (mk_real (treal_eq y0)).
Definition term13 := mk_real (treal_eq (treal_of_num (NUMERAL (BIT1 0)))).
Definition term25 (x0 : prod hreal hreal) := @eq real (real_mul (real_inv (mk_real (treal_eq x0))) (mk_real (treal_eq x0))).
Definition term2 := mk_real (treal_eq (treal_of_num (NUMERAL 0))).
Definition term27 := NUMERAL (BIT1 0).
Definition term16 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := mk_real (treal_eq (treal_mul x0 x1)).
