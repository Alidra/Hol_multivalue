Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : int) := and ((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term22 := real_of_int (int_of_num (NUMERAL 0)).
Definition term21 := real_of_num (NUMERAL 0).
Definition term28 := int_of_num (NUMERAL 0).
Definition term27 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term24 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : int) := and ((real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : int) := real_of_int (int_abs x0).
Definition term38 (x0 : int) := forall y0 : nat, ((int_pow x0 y0) = (int_of_num (NUMERAL (BIT1 0)))) = ((((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even y0)) \/ (y0 = (NUMERAL 0))).
Definition term1 (x0 : int) := forall y0 : nat, ((real_pow (real_of_int x0) y0) = (real_of_num (NUMERAL (BIT1 0)))) = ((((real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even y0)) \/ (y0 = (NUMERAL 0))).
Definition term30 (x0 : int) := imp (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term9 (x0 : nat) := real_of_int (int_of_num x0).
Definition term33 (x0 : int) (x1 : nat) := ((real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL (BIT1 0)))) = ((((real_abs y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt y0 (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even y1)) \/ (y1 = (NUMERAL 0)))) (real_of_int x0).
Definition term17 (x0 : int) := @eq real (real_abs (real_of_int x0)).
Definition term34 (x0 : int) (x1 : nat) := ((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1).
Definition term26 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term14 (x0 : int) (x1 : nat) := @eq Prop ((int_pow x0 x1) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term29 (x0 : int) := imp (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term32 (x0 : int) (x1 : nat) := (int_lt x0 (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1.
Definition term25 (x0 : int) := real_lt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term39 := forall y0 : int, forall y1 : nat, ((int_pow y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((((int_abs y0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_lt y0 (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even y1)) \/ (y1 = (NUMERAL 0))).
Definition term3 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term37 (x0 : int) (x1 : nat) := (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1)) \/ (x1 = (NUMERAL 0)).
Definition term5 (x0 : int) (x1 : nat) := (((real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1)) \/ (x1 = (NUMERAL 0)).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => ((real_pow (real_of_int x0) y0) = (real_of_num (NUMERAL (BIT1 0)))) = ((((real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even y0)) \/ (y0 = (NUMERAL 0)))) x1.
Definition term36 (x0 : int) (x1 : nat) := or (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_lt x0 (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term35 (x0 : int) (x1 : nat) := or (((real_abs (real_of_int x0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term4 := real_of_num (NUMERAL (BIT1 0)).
Definition term31 (x0 : int) (x1 : nat) := (real_lt (real_of_int x0) (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even x1.
Definition term7 (x0 : int) (x1 : nat) := @eq real (real_pow (real_of_int x0) x1).
Definition term8 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow x0 x1)).
Definition term23 (x0 : int) := real_lt (real_of_int x0).
Definition term10 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term15 (x0 : int) := real_abs (real_of_int x0).
Definition term6 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term13 (x0 : int) (x1 : nat) := @eq Prop ((real_pow (real_of_int x0) x1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 := int_of_num (NUMERAL (BIT1 0)).
Definition term18 (x0 : int) := @eq real (real_of_int (int_abs x0)).
Definition term11 := NUMERAL (BIT1 0).
