Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 := hreal_of_num (NUMERAL 0).
Definition term43 (x0 : hreal) := (fun y0 : hreal => (~ (y0 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y0) y0) = (hreal_of_num (NUMERAL (BIT1 0)))) x0.
Definition term2 := mk_hreal (nadd_eq (nadd_of_num (NUMERAL 0))).
Definition term44 (x0 : hreal) := (~ (x0 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv x0) x0) = (hreal_of_num (NUMERAL (BIT1 0))).
Definition term33 := forall y0 : nadd, (~ ((mk_hreal (nadd_eq y0)) = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv (mk_hreal (nadd_eq y0))) (mk_hreal (nadd_eq y0))) = (hreal_of_num (NUMERAL (BIT1 0))).
Definition term32 := forall y0 : nadd, (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> nadd_eq (nadd_mul (nadd_inv y0) y0) (nadd_of_num (NUMERAL (BIT1 0))).
Definition term12 (x0 : nadd) := mk_hreal (nadd_eq (nadd_mul (nadd_inv x0) x0)).
Definition term26 := hreal_of_num (NUMERAL (BIT1 0)).
Definition term10 (x0 : nadd) := imp (~ ((mk_hreal (nadd_eq x0)) = (hreal_of_num (NUMERAL 0)))).
Definition term23 (x0 : nadd) := hreal_mul (hreal_inv (mk_hreal (nadd_eq x0))) (mk_hreal (nadd_eq x0)).
Definition term17 (x0 : nadd) (x1 : nadd) := hreal_mul (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term24 (x0 : nadd) := @eq hreal (mk_hreal (nadd_eq (nadd_mul (nadd_inv x0) x0))).
Definition term37 := forall y0 : hreal, (fun y1 : hreal => (~ (y1 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y1) y1) = (hreal_of_num (NUMERAL (BIT1 0)))) y0.
Definition term36 := forall y0 : nadd, (fun y1 : hreal => (~ (y1 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y1) y1) = (hreal_of_num (NUMERAL (BIT1 0)))) (mk_hreal (nadd_eq y0)).
Definition term20 (x0 : nadd) := hreal_inv (mk_hreal (nadd_eq x0)).
Definition term13 := mk_hreal (nadd_eq (nadd_of_num (NUMERAL (BIT1 0)))).
Definition term19 (x0 : nadd) := mk_hreal (nadd_eq (nadd_inv x0)).
Definition term15 := nadd_of_num (NUMERAL (BIT1 0)).
Definition term3 := nadd_of_num (NUMERAL 0).
Definition term4 (x0 : nat) := mk_hreal (nadd_eq (nadd_of_num x0)).
Definition term18 (x0 : nadd) := hreal_mul (mk_hreal (nadd_eq (nadd_inv x0))) (mk_hreal (nadd_eq x0)).
Definition term40 := fun y0 : nadd => (fun y1 : hreal => (~ (y1 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y1) y1) = (hreal_of_num (NUMERAL (BIT1 0)))) (mk_hreal (nadd_eq y0)).
Definition term28 (x0 : nadd) := (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))) -> nadd_eq (nadd_mul (nadd_inv x0) x0) (nadd_of_num (NUMERAL (BIT1 0))).
Definition term31 := fun y0 : nadd => (~ ((mk_hreal (nadd_eq y0)) = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv (mk_hreal (nadd_eq y0))) (mk_hreal (nadd_eq y0))) = (hreal_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term11 (x0 : nadd) := nadd_eq (nadd_mul (nadd_inv x0) x0) (nadd_of_num (NUMERAL (BIT1 0))).
Definition term42 := @eq Prop (forall y0 : nadd, (~ ((mk_hreal (nadd_eq y0)) = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv (mk_hreal (nadd_eq y0))) (mk_hreal (nadd_eq y0))) = (hreal_of_num (NUMERAL (BIT1 0)))).
Definition term1 (x0 : nadd) := nadd_eq x0 (nadd_of_num (NUMERAL 0)).
Definition term38 := fun y0 : hreal => (~ (y0 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y0) y0) = (hreal_of_num (NUMERAL (BIT1 0))).
Definition term45 := fun y0 : hreal => (fun y1 : hreal => (~ (y1 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y1) y1) = (hreal_of_num (NUMERAL (BIT1 0)))) y0.
Definition term14 (x0 : nadd) := nadd_mul (nadd_inv x0) x0.
Definition term6 (x0 : nadd) := @eq hreal (mk_hreal (nadd_eq x0)).
Definition term30 := fun y0 : nadd => (~ (nadd_eq y0 (nadd_of_num (NUMERAL 0)))) -> nadd_eq (nadd_mul (nadd_inv y0) y0) (nadd_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : nadd) := ~ ((mk_hreal (nadd_eq x0)) = (hreal_of_num (NUMERAL 0))).
Definition term39 (x0 : nadd) := (fun y0 : hreal => (~ (y0 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y0) y0) = (hreal_of_num (NUMERAL (BIT1 0)))) (mk_hreal (nadd_eq x0)).
Definition term29 (x0 : nadd) := (~ ((mk_hreal (nadd_eq x0)) = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv (mk_hreal (nadd_eq x0))) (mk_hreal (nadd_eq x0))) = (hreal_of_num (NUMERAL (BIT1 0))).
Definition term21 (x0 : nadd) := hreal_mul (mk_hreal (nadd_eq (nadd_inv x0))).
Definition term35 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term34 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term7 (x0 : nadd) := ~ (nadd_eq x0 (nadd_of_num (NUMERAL 0))).
Definition term46 := forall y0 : hreal, (~ (y0 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y0) y0) = (hreal_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : nadd) := imp (~ (nadd_eq x0 (nadd_of_num (NUMERAL 0)))).
Definition term25 (x0 : nadd) := @eq hreal (hreal_mul (hreal_inv (mk_hreal (nadd_eq x0))) (mk_hreal (nadd_eq x0))).
Definition term16 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_mul x0 x1)).
Definition term27 := NUMERAL (BIT1 0).
Definition term41 := @eq Prop (forall y0 : nadd, (fun y1 : hreal => (~ (y1 = (hreal_of_num (NUMERAL 0)))) -> (hreal_mul (hreal_inv y1) y1) = (hreal_of_num (NUMERAL (BIT1 0)))) (mk_hreal (nadd_eq y0))).
Definition term22 (x0 : nadd) := hreal_mul (hreal_inv (mk_hreal (nadd_eq x0))).
