Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term7 := real_pow (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : nat) := @eq real (real_of_int (int_pow (int_of_num (NUMERAL (BIT1 0))) x0)).
Definition term13 (x0 : nat) := @eq real (real_pow (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term3 (x0 : nat) := real_of_int (int_of_num x0).
Definition term8 (x0 : nat) := real_pow (real_of_int (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term16 := forall y0 : nat, (int_pow (int_of_num (NUMERAL (BIT1 0))) y0) = (int_of_num (NUMERAL (BIT1 0))).
Definition term6 := real_pow (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term15 (x0 : nat) := int_pow (int_of_num (NUMERAL (BIT1 0))) x0.
Definition term2 := real_of_num (NUMERAL (BIT1 0)).
Definition term0 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term4 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : nat) := real_of_int (int_pow (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term10 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term12 := int_of_num (NUMERAL (BIT1 0)).
Definition term5 := NUMERAL (BIT1 0).
