Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term71 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term54 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) /\ (x0 = x1)) -> ~ (y0 /\ x1)) False.
Definition term70 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (~ x0) /\ (x1 = x2).
Definition term61 (x0 : Prop) (x1 : Prop) := (~ False) /\ (x0 = x1).
Definition term17 (x0 : Prop) := and (True = x0).
Definition term67 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 = x2) /\ (x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3)) -> ((x0 = x2) /\ (x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3).
Definition term55 (x0 : Prop) (x1 : Prop) := ((~ False) /\ (x0 = x1)) -> ~ (False /\ x1).
Definition term5 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3))) -> ((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term50 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ y0) /\ (x0 = x1)) -> ~ (y0 /\ x1)) True.
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop (((x0 = x2) /\ (x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3)).
Definition term34 (x0 : Prop) (x1 : Prop) := imp (x0 = x1).
Definition term81 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le (real_div x2 x3) (real_div x0 x1)) /\ (real_le (real_div x0 x1) (real_div x2 x3))).
Definition term78 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 = x1) /\ (x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) True.
Definition term39 (x0 : Prop) := and (False = x0).
Definition term37 (x0 : Prop) (x1 : Prop) := imp (False /\ (x0 = x1)).
Definition term44 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((~ x0) /\ (x1 = x2)).
Definition term48 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((~ y0) /\ (x0 = x1)) -> ~ (y0 /\ x1).
Definition term21 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (x0 /\ (x1 = x2)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term46 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term76 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term75 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term85 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term83 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((real_le (real_div x2 x1) (real_div x0 x3)) = (real_le (real_mul x2 x3) (real_mul x0 x1))) /\ ((real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3)))) -> ((real_le (real_div x2 x1) (real_div x0 x3)) /\ (real_le (real_div x0 x3) (real_div x2 x1))) = ((real_le (real_mul x2 x3) (real_mul x0 x1)) /\ (real_le (real_mul x0 x1) (real_mul x2 x3))).
Definition term27 (x0 : Prop) (x1 : Prop) := (True /\ (x0 = x1)) -> x0 = (True /\ x1).
Definition term29 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x1 /\ (x0 = x2)) -> x0 = (x1 /\ x2)).
Definition term31 (x0 : Prop) (x1 : Prop) := (False /\ (x0 = x1)) -> x0 = (False /\ x1).
Definition term86 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le (real_div x2 x1) (real_div x0 x3)) = (real_le (real_mul x2 x3) (real_mul x0 x1))) /\ ((real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3))).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((False = x1) /\ (x0 = x2)) -> (False /\ x0) = (x1 /\ x2).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((True = x1) /\ (x0 = x2)) -> (True /\ x0) = (x1 /\ x2).
Definition term74 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term3 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_le (real_mul x0 x1) (real_mul x2 x3).
Definition term68 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term62 (x0 : Prop) (x1 : Prop) := imp ((~ False) /\ (x0 = x1)).
Definition term41 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False = x0) /\ (x1 = x2).
Definition term47 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((~ x1) /\ (x0 = x2)) -> ~ (x1 /\ x2).
Definition term58 (x0 : Prop) (x1 : Prop) := imp ((~ True) /\ (x0 = x1)).
Definition term22 (x0 : Prop) := @eq Prop (True /\ x0).
Definition term56 := and (~ True).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := fun y0 : Prop => ((y0 = x1) /\ (x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2).
Definition term35 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 = x1.
Definition term73 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term53 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((~ x1) /\ (x0 = x2)) -> ~ (x1 /\ x2)).
Definition term66 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 = x2) /\ (x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3)) -> (x0 /\ x1) = (x2 /\ x3).
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x1 /\ (x0 = x2)) -> x0 = (x1 /\ x2).
Definition term24 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 /\ (x0 = x1)) -> x0 = (y0 /\ x1).
Definition term80 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_div x0 x1) = (real_div x2 x3)).
Definition term77 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term63 (x0 : Prop) := ~ (False /\ x0).
Definition term1 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term4 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (((real_lt (real_of_num (NUMERAL 0)) x3) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> (real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3))) -> (real_le (real_div x0 x3) (real_div x2 x1)) = (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 = x2).
Definition term79 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_div x2 x3) (real_div x0 x1)) /\ (real_le (real_div x0 x1) (real_div x2 x3)).
Definition term49 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((~ y0) /\ (x0 = x1)) -> ~ (y0 /\ x1)) x2.
Definition term69 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term7 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term38 (x0 : Prop) := False -> ~ x0.
Definition term45 (x0 : Prop) := @eq Prop (False /\ x0).
Definition term65 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x1) /\ (x2 = x3).
Definition term25 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 /\ (x0 = x1)) -> x0 = (y0 /\ x1)) x2.
Definition term84 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x0 = x2) /\ (x1 = x3)) -> (x0 /\ x1) = (x2 /\ x3).
Definition term40 (x0 : Prop) := and (~ x0).
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 = x1) /\ (x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) x3).
Definition term2 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_le (real_div x0 x1) (real_div x2 x3).
Definition term9 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((y0 = x1) /\ (x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) x3.
Definition term32 (x0 : Prop) (x1 : Prop) := True /\ (x0 = x1).
Definition term51 (x0 : Prop) (x1 : Prop) := ((~ True) /\ (x0 = x1)) -> ~ (True /\ x1).
Definition term26 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 /\ (x0 = x1)) -> x0 = (y0 /\ x1)) True.
Definition term64 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> True.
Definition term15 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 = x1) /\ (x0 = x2)) -> (y0 /\ x0) = (x1 /\ x2)) False.
Definition term30 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 /\ (x0 = x1)) -> x0 = (y0 /\ x1)) False.
Definition term60 := and (~ False).
Definition term82 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_mul x2 x3) (real_mul x0 x1)) /\ (real_le (real_mul x0 x1) (real_mul x2 x3)).
Definition term72 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term43 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((False = x0) /\ (x1 = x2)).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((True = x0) /\ (x1 = x2)).
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True = x0) /\ (x1 = x2).
Definition term6 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term57 (x0 : Prop) (x1 : Prop) := (~ True) /\ (x0 = x1).
Definition term33 (x0 : Prop) (x1 : Prop) := imp (True /\ (x0 = x1)).
Definition term36 (x0 : Prop) (x1 : Prop) := False /\ (x0 = x1).
Definition term52 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) /\ (x0 = x1)) -> ~ (y0 /\ x1)) x2).
Definition term28 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 /\ (x0 = x1)) -> x0 = (y0 /\ x1)) x2).
Definition term59 (x0 : Prop) := ~ (True /\ x0).
