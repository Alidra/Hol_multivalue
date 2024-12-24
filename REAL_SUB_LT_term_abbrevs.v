Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term40 (x0 : real) (x1 : real) := real_le (real_neg (real_sub x0 x1)).
Definition term52 (x0 : real) (x1 : real) := @eq Prop (~ (real_le x0 x1)).
Definition term9 (x0 : real) (x1 : real) := real_le (real_neg x0) x1.
Definition term43 (x0 : real) (x1 : real) := ~ (real_le (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL 0))).
Definition term28 := real_of_num (NUMERAL 0).
Definition term42 (x0 : real) (x1 : real) := real_le (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL 0)).
Definition term50 (x0 : real) (x1 : real) := real_add (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term55 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term29 (x0 : real) (x1 : real) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term53 := fun y0 : real => True.
Definition term49 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term54 := forall y0 : real, True.
Definition term56 (x0 : Prop) := forall y0 : real, x0.
Definition term5 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_le y0 x0)) x1.
Definition term39 (x0 : real) (x1 : real) := real_le (real_sub x0 x1).
Definition term46 (x0 : real) := forall y0 : real, (~ (real_le (real_neg (real_sub y0 x0)) (real_of_num (NUMERAL 0)))) = (~ (real_le x0 y0)).
Definition term34 (x0 : real) := forall y0 : real, (~ (real_le (real_sub x0 y0) (real_of_num (NUMERAL 0)))) = (~ (real_le x0 y0)).
Definition term48 := forall y0 : real, forall y1 : real, (~ (real_le (real_neg (real_sub y1 y0)) (real_of_num (NUMERAL 0)))) = (~ (real_le y0 y1)).
Definition term38 := forall y0 : real, forall y1 : real, (~ (real_le (real_sub y0 y1) (real_of_num (NUMERAL 0)))) = (~ (real_le y0 y1)).
Definition term37 := forall y0 : real, forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_lt y1 y0).
Definition term19 := forall y0 : real, forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1)).
Definition term18 := forall y0 : real, forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub y0 x0) = (real_neg (real_sub x0 y0))) x1.
Definition term51 := real_le (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term14 (x0 : real) := forall y0 : real, (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term12 (x0 : real) := fun y0 : real => (real_neg (real_sub x0 y0)) = (real_sub y0 x0).
Definition term26 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term45 (x0 : real) := fun y0 : real => (~ (real_le (real_neg (real_sub y0 x0)) (real_of_num (NUMERAL 0)))) = (~ (real_le x0 y0)).
Definition term32 (x0 : real) := fun y0 : real => (~ (real_le (real_sub x0 y0) (real_of_num (NUMERAL 0)))) = (~ (real_le x0 y0)).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0))) x1.
Definition term35 := fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_lt y1 y0).
Definition term16 := fun y0 : real => forall y1 : real, (real_neg (real_sub y0 y1)) = (real_sub y1 y0).
Definition term33 (x0 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_lt y0 x0).
Definition term1 (x0 : real) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_le y0 x0).
Definition term27 (x0 : real) (x1 : real) := ~ (real_le (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1))) x0.
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_neg y0) y1) = (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_of_num (NUMERAL 0)) (real_sub y0 y1)) = (real_le y1 y0)) x0.
Definition term13 (x0 : real) := fun y0 : real => (real_sub y0 x0) = (real_neg (real_sub x0 y0)).
Definition term15 (x0 : real) := forall y0 : real, (real_sub y0 x0) = (real_neg (real_sub x0 y0)).
Definition term10 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term23 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term30 (x0 : real) (x1 : real) := @eq Prop (~ (real_le (real_sub x0 x1) (real_of_num (NUMERAL 0)))).
Definition term25 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term44 (x0 : real) (x1 : real) := @eq Prop (~ (real_le (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL 0)))).
Definition term31 (x0 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_sub x0 y0)) = (real_lt y0 x0).
Definition term11 (x0 : real) (x1 : real) := real_neg (real_sub x0 x1).
Definition term41 (x0 : real) (x1 : real) := real_le (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) := forall y0 : real, (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term4 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term47 := fun y0 : real => forall y1 : real, (~ (real_le (real_neg (real_sub y1 y0)) (real_of_num (NUMERAL 0)))) = (~ (real_le y0 y1)).
Definition term36 := fun y0 : real => forall y1 : real, (~ (real_le (real_sub y0 y1) (real_of_num (NUMERAL 0)))) = (~ (real_le y0 y1)).
Definition term17 := fun y0 : real => forall y1 : real, (real_sub y1 y0) = (real_neg (real_sub y0 y1)).
