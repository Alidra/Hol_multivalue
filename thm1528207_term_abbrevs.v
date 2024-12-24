Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term3 := real_of_num (NUMERAL 0).
Definition term56 := real_sub (real_neg (real_of_num (NUMERAL 0))).
Definition term65 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term32 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL 0)))).
Definition term2 := real_abs (real_of_num (NUMERAL 0)).
Definition term20 := real_gt (real_abs (real_of_num (NUMERAL 0))).
Definition term55 := real_neg (real_of_num (NUMERAL 0)).
Definition term58 := real_sub (real_neg (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term42 := @eq Prop (real_gt (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term22 := real_gt (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term46 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term24 := or (real_gt (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term6 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term0 := ~ ((real_abs (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term26 := (fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_abs (real_of_num (NUMERAL 0))).
Definition term10 := real_add (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term13 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL 0))).
Definition term31 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term30 := real_gt (real_neg (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term28 := fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0)).
Definition term70 := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term38 := (real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term1 := (real_gt (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term29 := (fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL 0))).
Definition term76 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term7 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term57 := real_sub (real_of_num (NUMERAL 0)).
Definition term16 := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL 0)))).
Definition term18 := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term35 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term59 := real_gt (real_sub (real_neg (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term11 := real_neg (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term37 := (real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term27 := ((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL 0))))).
Definition term12 := real_neg (real_abs (real_of_num (NUMERAL 0))).
Definition term60 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term17 := real_gt (real_neg (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term15 := real_gt (real_neg (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))).
Definition term61 := ((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term41 := ((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))).
Definition term75 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term69 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term25 := (real_gt (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term67 := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term73 := or (((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term5 := real_add (real_abs (real_of_num (NUMERAL 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term19 := real_gt (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term39 := or ((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))).
Definition term9 := real_add (real_abs (real_of_num (NUMERAL 0))).
Definition term14 := @eq real (real_neg (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)))).
Definition term62 (x0 : real) (x1 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1.
Definition term64 := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term43 := real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term36 := and (real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term72 := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term44 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term77 := (~ ((real_abs (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> False.
Definition term54 := real_gt (real_sub (real_neg (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term51 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term21 := real_gt (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term66 := real_of_num (NUMERAL (BIT1 0)).
Definition term50 := real_ge (real_of_num (NUMERAL 0)).
Definition term71 := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term68 := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term23 := or (real_gt (real_sub (real_abs (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term40 := or ((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term74 := (((real_ge (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term33 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term49 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term52 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term48 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term34 := (fun y0 : real => real_gt y0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term47 := real_add (real_of_num (NUMERAL 0)).
Definition term8 := NUMERAL (BIT1 0).
Definition term45 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term53 := real_gt (real_of_num (NUMERAL 0)).
