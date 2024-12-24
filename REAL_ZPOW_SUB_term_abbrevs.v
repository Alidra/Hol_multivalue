Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 (x0 : real) := fun y0 : int => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_sub y0 y1)) = (real_div (real_zpow x0 y0) (real_zpow x0 y1)).
Definition term11 (x0 : real) (x1 : int) := (fun y0 : int => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1))) x1.
Definition term49 (x0 : int) (x1 : real) := forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 y0)) = (real_div (real_zpow x1 x0) (real_zpow x1 y0)).
Definition term12 (x0 : int) (x1 : real) := forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add x0 y0)) = (real_mul (real_zpow x1 x0) (real_zpow x1 y0)).
Definition term35 := real_of_num (NUMERAL 0).
Definition term34 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term51 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term48 := fun y0 : int => True.
Definition term7 (x0 : real) (x1 : int) := real_zpow x0 (int_neg x1).
Definition term36 (x0 : real) (x1 : int) (x2 : int) := real_zpow x0 (int_add x1 (int_neg x2)).
Definition term18 (x0 : int) := (fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1))) x0.
Definition term56 := fun y0 : real => True.
Definition term40 (x0 : int) (x1 : real) (x2 : int) := real_mul (real_zpow x1 x0) (real_inv (real_zpow x1 x2)).
Definition term58 := forall y0 : real, True.
Definition term59 (x0 : Prop) := forall y0 : real, x0.
Definition term27 (x0 : int) (x1 : real) (x2 : int) := real_div (real_zpow x1 x0) (real_zpow x1 x2).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term46 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> True.
Definition term57 := forall y0 : real, forall y1 : int, forall y2 : int, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_sub y1 y2)) = (real_div (real_zpow y0 y1) (real_zpow y0 y2)).
Definition term28 (x0 : int) (x1 : real) (x2 : int) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (x1 = (real_of_num (NUMERAL 0)))) = y0) -> (y0 -> ((real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = y1) -> ((~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = (y0 -> y1)) x3.
Definition term55 := fun y0 : real => forall y1 : int, forall y2 : int, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_sub y1 y2)) = (real_div (real_zpow y0 y1) (real_zpow y0 y2)).
Definition term15 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term13 (x0 : int) (x1 : real) (x2 : int) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add x0 y0)) = (real_mul (real_zpow x1 x0) (real_zpow x1 y0))) x2.
Definition term31 (x0 : int) (x1 : real) (x2 : int) (x3 : Prop) (x4 : Prop) := ((~ (x1 = (real_of_num (NUMERAL 0)))) = x3) -> (x3 -> ((real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = x4) -> ((~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = (x3 -> x4).
Definition term6 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0))) x1.
Definition term47 (x0 : int) (x1 : real) := fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 y0)) = (real_div (real_zpow x1 x0) (real_zpow x1 y0)).
Definition term22 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term5 (x0 : real) := forall y0 : int, (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0)).
Definition term14 (x0 : int) (x1 : real) (x2 : int) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add x0 x2)) = (real_mul (real_zpow x1 x0) (real_zpow x1 x2)).
Definition term20 (x0 : int) (x1 : int) := (fun y0 : int => (int_sub x0 y0) = (int_add x0 (int_neg y0))) x1.
Definition term8 (x0 : real) (x1 : int) := real_inv (real_zpow x0 x1).
Definition term32 (x0 : int) (x1 : int) (x2 : real) (x3 : Prop) := ((~ (x2 = (real_of_num (NUMERAL 0)))) = (~ (x2 = (real_of_num (NUMERAL 0))))) -> ((~ (x2 = (real_of_num (NUMERAL 0)))) -> ((real_zpow x2 (int_sub x0 x1)) = (real_div (real_zpow x2 x0) (real_zpow x2 x1))) = x3) -> ((~ (x2 = (real_of_num (NUMERAL 0)))) -> (real_zpow x2 (int_sub x0 x1)) = (real_div (real_zpow x2 x0) (real_zpow x2 x1))) = ((~ (x2 = (real_of_num (NUMERAL 0)))) -> x3).
Definition term52 (x0 : Prop) := forall y0 : int, x0.
Definition term26 (x0 : real) (x1 : int) (x2 : int) := real_zpow x0 (int_sub x1 x2).
Definition term54 (x0 : real) := forall y0 : int, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_sub y0 y1)) = (real_div (real_zpow x0 y0) (real_zpow x0 y1)).
Definition term10 (x0 : real) := forall y0 : int, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1)).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : int, forall y2 : int, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add y1 y2)) = (real_mul (real_zpow y0 y1) (real_zpow y0 y2))) x0.
Definition term39 (x0 : real) (x1 : int) := real_mul (real_zpow x0 x1).
Definition term29 (x0 : int) (x1 : real) (x2 : int) (x3 : Prop) := forall y0 : Prop, ((~ (x1 = (real_of_num (NUMERAL 0)))) = x3) -> (x3 -> ((real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = y0) -> ((~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = (x3 -> y0).
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term1 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term25 (x0 : int) (x1 : real) (x2 : int) := forall y0 : Prop, forall y1 : Prop, ((~ (x1 = (real_of_num (NUMERAL 0)))) = y0) -> (y0 -> ((real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = y1) -> ((~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = (y0 -> y1).
Definition term24 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term17 (x0 : int) (x1 : real) (x2 : int) := real_mul (real_zpow x1 x0) (real_zpow x1 x2).
Definition term42 (x0 : int) (x1 : real) (x2 : int) := @eq real (real_mul (real_zpow x1 x0) (real_inv (real_zpow x1 x2))).
Definition term30 (x0 : int) (x1 : real) (x2 : int) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((~ (x1 = (real_of_num (NUMERAL 0)))) = x3) -> (x3 -> ((real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = y0) -> ((~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = (x3 -> y0)) x4.
Definition term38 (x0 : int) (x1 : real) (x2 : int) := real_mul (real_zpow x1 x0) (real_zpow x1 (int_neg x2)).
Definition term33 (x0 : int) (x1 : int) (x2 : real) (x3 : Prop) := ((~ (x2 = (real_of_num (NUMERAL 0)))) -> ((real_zpow x2 (int_sub x0 x1)) = (real_div (real_zpow x2 x0) (real_zpow x2 x1))) = x3) -> ((~ (x2 = (real_of_num (NUMERAL 0)))) -> (real_zpow x2 (int_sub x0 x1)) = (real_div (real_zpow x2 x0) (real_zpow x2 x1))) = ((~ (x2 = (real_of_num (NUMERAL 0)))) -> x3).
Definition term50 := forall y0 : int, True.
Definition term21 (x0 : int) (x1 : int) := int_add x0 (int_neg x1).
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 (int_neg y1)) = (real_inv (real_zpow y0 y1))) x0.
Definition term44 (x0 : int) (x1 : int) (x2 : real) := ((~ (x2 = (real_of_num (NUMERAL 0)))) -> ((real_zpow x2 (int_sub x0 x1)) = (real_div (real_zpow x2 x0) (real_zpow x2 x1))) = True) -> ((~ (x2 = (real_of_num (NUMERAL 0)))) -> (real_zpow x2 (int_sub x0 x1)) = (real_div (real_zpow x2 x0) (real_zpow x2 x1))) = ((~ (x2 = (real_of_num (NUMERAL 0)))) -> True).
Definition term45 (x0 : int) (x1 : real) (x2 : int) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2)).
Definition term41 (x0 : real) (x1 : int) (x2 : int) := @eq real (real_zpow x0 (int_sub x1 x2)).
Definition term3 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term43 (x0 : int) (x1 : real) (x2 : int) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> ((real_zpow x1 (int_sub x0 x2)) = (real_div (real_zpow x1 x0) (real_zpow x1 x2))) = True.
Definition term19 (x0 : int) := forall y0 : int, (int_sub x0 y0) = (int_add x0 (int_neg y0)).
Definition term37 (x0 : int) (x1 : real) (x2 : int) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add x0 (int_neg x2))) = (real_mul (real_zpow x1 x0) (real_zpow x1 (int_neg x2))).
Definition term16 (x0 : real) (x1 : int) (x2 : int) := real_zpow x0 (int_add x1 x2).
