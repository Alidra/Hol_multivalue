Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term36 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term58 (x0 : nat) := @eq Prop (~ (x0 = (NUMERAL 0))).
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term38 (x0 : nat) (x1 : nat) := @eq Prop (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term60 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term9 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) = (~ (int_le y1 y0))) x0.
Definition term53 (x0 : nat) := ~ (False /\ (x0 = (NUMERAL 0))).
Definition term57 (x0 : nat) := @eq Prop (~ (True /\ (x0 = (NUMERAL 0)))).
Definition term42 (x0 : nat) (x1 : nat) := ((int_lt (int_of_num x0) (int_neg (int_of_num x1))) = False) /\ (((int_lt (int_of_num x0) (int_of_num x1)) = (Peano.lt x0 x1)) /\ (((int_lt (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (Peano.lt x1 x0)) /\ ((int_lt (int_neg (int_of_num x0)) (int_of_num x1)) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))))).
Definition term20 (x0 : nat) (x1 : nat) := and ((int_lt (int_of_num x0) (int_neg (int_of_num x1))) = False).
Definition term22 (x0 : nat) (x1 : nat) := ~ (int_le (int_of_num x0) (int_of_num x1)).
Definition term50 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) (x1 = (NUMERAL 0))).
Definition term28 (x0 : nat) (x1 : nat) := ~ (int_le (int_neg (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term12 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term55 (x0 : nat) := True /\ (x0 = (NUMERAL 0)).
Definition term45 (x0 : nat) := fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0)).
Definition term35 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term56 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term54 (x0 : nat) := ~ ((x0 = (NUMERAL 0)) /\ False).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term17 (x0 : nat) (x1 : nat) := ~ (int_le (int_neg (int_of_num x0)) (int_of_num x1)).
Definition term59 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term51 (x0 : nat) (x1 : nat) := @eq Prop ((~ ((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term19 (x0 : nat) (x1 : nat) := int_le (int_neg (int_of_num x0)) (int_of_num x1).
Definition term61 (x0 : nat) := @eq Prop (~ (False /\ (x0 = (NUMERAL 0)))).
Definition term27 (x0 : nat) (x1 : nat) := int_lt (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term29 (x0 : nat) (x1 : nat) := int_le (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term10 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (~ (int_le y0 x0)).
Definition term32 (x0 : nat) (x1 : nat) := int_lt (int_neg (int_of_num x0)) (int_of_num x1).
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) (x1 = (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) := and ((int_lt (int_of_num x0) (int_of_num x1)) = (Peano.lt x0 x1)).
Definition term62 (x0 : nat) := (x0 = (NUMERAL 0)) /\ False.
Definition term52 (x0 : nat) := (fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) False.
Definition term16 (x0 : nat) (x1 : nat) := ~ (int_lt (int_of_num x0) (int_neg (int_of_num x1))).
Definition term24 (x0 : nat) (x1 : nat) := @eq Prop (int_lt (int_of_num x0) (int_of_num x1)).
Definition term39 (x0 : nat) (x1 : nat) := ((int_lt (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (Peano.lt x1 x0)) /\ ((int_lt (int_neg (int_of_num x0)) (int_of_num x1)) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term18 (x0 : nat) := int_neg (int_of_num x0).
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term33 (x0 : nat) (x1 : nat) := ~ (int_le (int_of_num x0) (int_neg (int_of_num x1))).
Definition term15 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_neg (int_of_num x1)).
Definition term47 (x0 : nat) := (fun y0 : Prop => (~ (y0 /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ y0))) True.
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term40 (x0 : nat) (x1 : nat) := True /\ ((~ ((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0)))) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term25 (x0 : nat) (x1 : nat) := @eq Prop (~ (Peano.le x0 x1)).
Definition term43 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term34 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_neg (int_of_num x1)).
Definition term23 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term30 (x0 : nat) (x1 : nat) := @eq Prop (int_lt (int_neg (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term31 (x0 : nat) (x1 : nat) := and ((int_lt (int_neg (int_of_num x1)) (int_neg (int_of_num x0))) = (Peano.lt x0 x1)).
Definition term48 (x0 : nat) := ~ (True /\ (x0 = (NUMERAL 0))).
Definition term37 (x0 : nat) (x1 : nat) := @eq Prop (int_lt (int_neg (int_of_num x0)) (int_of_num x1)).
Definition term11 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) = (~ (int_le y0 x0))) x1.
Definition term49 (x0 : nat) := ~ ((x0 = (NUMERAL 0)) /\ True).
Definition term44 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
Definition term41 (x0 : nat) (x1 : nat) := ((int_lt (int_of_num x0) (int_of_num x1)) = (Peano.lt x0 x1)) /\ (((int_lt (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (Peano.lt x1 x0)) /\ ((int_lt (int_neg (int_of_num x0)) (int_of_num x1)) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
