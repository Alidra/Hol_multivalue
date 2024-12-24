Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term0 (x0 : real) (x1 : real) := real_le (real_neg x0) x1.
Definition term3 (x0 : real) := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)) = (real_le (real_neg x0) y0).
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 := fun y0 : real => True.
Definition term23 (x0 : real) (x1 : real) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term28 := forall y0 : real, True.
Definition term30 (x0 : Prop) := forall y0 : real, x0.
Definition term32 := forall y0 : real, forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_le y1 y0).
Definition term9 := forall y0 : real, forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)) = (real_le (real_neg y0) y1).
Definition term8 := forall y0 : real, forall y1 : real, (real_le (real_neg y0) y1) = (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term20 := real_le (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) (x1 : real) := real_le (real_neg x0) (real_neg x1).
Definition term21 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term6 := fun y0 : real => forall y1 : real, (real_le (real_neg y0) y1) = (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term5 (x0 : real) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)) = (real_le (real_neg x0) y0).
Definition term24 (x0 : real) (x1 : real) := @eq Prop (real_le x0 x1).
Definition term31 := fun y0 : real => forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_le y1 y0).
Definition term7 := fun y0 : real => forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)) = (real_le (real_neg y0) y1).
Definition term27 (x0 : real) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_le y0 x0).
Definition term11 (x0 : real) := forall y0 : real, (real_le (real_neg x0) (real_neg y0)) = (real_le y0 x0).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)) = (real_le (real_neg y0) y1)) x0.
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_neg y0) (real_neg y1)) = (real_le y1 y0)) x0.
Definition term25 (x0 : real) := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_le y0 x0).
Definition term17 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term1 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term22 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 (real_neg x1)).
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_neg x0) (real_neg y0)) = (real_le y0 x0)) x1.
Definition term4 (x0 : real) := forall y0 : real, (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term2 (x0 : real) := fun y0 : real => (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)) = (real_le (real_neg x0) y0)) x1.
