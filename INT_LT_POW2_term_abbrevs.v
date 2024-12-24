Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term4 := real_of_int (int_of_num (NUMERAL 0)).
Definition term3 := real_of_num (NUMERAL 0).
Definition term21 := int_of_num (NUMERAL 0).
Definition term18 (x0 : nat) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term11 := real_pow (real_of_int (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term0 (x0 : nat) := (fun y0 : nat => real_lt (real_of_num (NUMERAL 0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) x0.
Definition term22 (x0 : nat) := int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term8 := real_of_int (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term5 := real_lt (real_of_num (NUMERAL 0)).
Definition term2 (x0 : nat) := real_of_int (int_of_num x0).
Definition term19 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term13 (x0 : nat) := real_pow (real_of_int (int_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term14 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term7 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term6 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term9 := NUMERAL (BIT0 (BIT1 0)).
Definition term20 (x0 : nat) := int_lt (int_of_num (NUMERAL 0)) (int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term23 := forall y0 : nat, int_lt (int_of_num (NUMERAL 0)) (int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term17 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term16 (x0 : nat) := real_of_int (int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term15 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term10 := real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term1 (x0 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
