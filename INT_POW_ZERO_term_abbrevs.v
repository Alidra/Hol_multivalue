Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term20 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term7 := real_pow (real_of_int (int_of_num (NUMERAL 0))).
Definition term24 (x0 : nat) := real_of_int (@COND int (x0 = (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
Definition term5 := real_of_int (int_of_num (NUMERAL 0)).
Definition term4 := real_of_num (NUMERAL 0).
Definition term12 := int_of_num (NUMERAL 0).
Definition term19 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term27 (x0 : nat) := @COND int (x0 = (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)).
Definition term26 (x0 : nat) := int_pow (int_of_num (NUMERAL 0)) x0.
Definition term14 (x0 : nat) := @eq real (real_of_int (int_pow (int_of_num (NUMERAL 0)) x0)).
Definition term23 (x0 : Prop) (x1 : int) (x2 : int) := real_of_int (@COND int x0 x1 x2).
Definition term18 (x0 : nat) := @COND real (x0 = (NUMERAL 0)).
Definition term13 (x0 : nat) := @eq real (real_pow (real_of_num (NUMERAL 0)) x0).
Definition term3 (x0 : nat) := real_of_int (int_of_num x0).
Definition term28 := forall y0 : nat, (int_pow (int_of_num (NUMERAL 0)) y0) = (@COND int (y0 = (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
Definition term0 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0.
Definition term9 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term22 (x0 : Prop) (x1 : int) (x2 : int) := @COND real x0 (real_of_int x1) (real_of_int x2).
Definition term15 := real_of_num (NUMERAL (BIT1 0)).
Definition term8 (x0 : nat) := real_pow (real_of_int (int_of_num (NUMERAL 0))) x0.
Definition term16 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : nat) := real_of_int (int_pow (int_of_num (NUMERAL 0)) x0).
Definition term1 (x0 : nat) := real_pow (real_of_num (NUMERAL 0)) x0.
Definition term10 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term6 := real_pow (real_of_num (NUMERAL 0)).
Definition term25 := int_of_num (NUMERAL (BIT1 0)).
Definition term17 := NUMERAL (BIT1 0).
