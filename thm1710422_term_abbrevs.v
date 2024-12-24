Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 := ~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))).
Definition term54 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term8 := real_of_num (NUMERAL 0).
Definition term25 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = ((x2 /\ x1) \/ ((~ x2) /\ x3)).
Definition term69 := and (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term23 := ((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) = True) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))).
Definition term79 := ((~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) -> False) -> (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)).
Definition term10 := @COND real False (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term59 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term16 := ((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) = False) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = False.
Definition term1 := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term49 := real_neg (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term35 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term77 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term53 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term36 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term11 := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term30 := or ((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))).
Definition term9 := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term12 := @COND real False (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term70 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term71 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term55 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term44 := (real_gt (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term75 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term37 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term14 := @eq real (real_of_num (NUMERAL 0)).
Definition term26 := ((((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) = False) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = False) /\ (((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) = True) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))))) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = (((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ False)).
Definition term61 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term43 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term62 := real_gt (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term51 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term73 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term17 := @COND real True (real_of_num (NUMERAL (BIT1 0))).
Definition term60 := real_gt (real_neg (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term58 := real_gt (real_neg (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term72 := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term74 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term32 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0)))).
Definition term5 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term50 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term48 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term57 := @eq real (real_neg (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term0 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term45 := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term52 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term13 := @eq real (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term46 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term78 := (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) -> False.
Definition term28 := (~ (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ False.
Definition term24 := (((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) = False) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = False) /\ (((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) = True) -> (~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0)))) = (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))).
Definition term20 := @COND real True (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 := real_gt (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term33 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term56 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term2 := real_of_num (NUMERAL (BIT1 0)).
Definition term3 := @COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term4 := @COND real False (real_of_num (NUMERAL (BIT1 0))).
Definition term66 := or (real_gt (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term68 := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term47 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term29 := ~ (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term76 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term41 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term67 := or (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term63 := real_gt (real_of_num (NUMERAL (BIT1 0))).
Definition term21 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term40 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term19 := @COND real True (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term7 := @COND real False (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term27 := ((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ False).
Definition term18 := @COND real True (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term15 := ~ ((@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))) (@COND real (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) = (real_of_num (NUMERAL 0))).
Definition term39 := real_add (real_of_num (NUMERAL 0)).
Definition term31 := ((real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (~ ((real_of_num (NUMERAL (BIT1 0))) = (real_of_num (NUMERAL 0))))) \/ False.
Definition term38 := NUMERAL (BIT1 0).
Definition term34 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term65 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term42 := real_gt (real_of_num (NUMERAL 0)).
