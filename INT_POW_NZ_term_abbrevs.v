Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) := imp (~ ((real_of_int x0) = (real_of_num (NUMERAL 0)))).
Definition term6 := real_of_int (int_of_num (NUMERAL 0)).
Definition term5 := real_of_num (NUMERAL 0).
Definition term8 := int_of_num (NUMERAL 0).
Definition term9 (x0 : int) := ~ ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => (~ ((real_of_int x0) = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow (real_of_int x0) y0) = (real_of_num (NUMERAL 0)))) x1.
Definition term18 (x0 : int) (x1 : nat) := ~ ((int_pow x0 x1) = (int_of_num (NUMERAL 0))).
Definition term3 (x0 : int) (x1 : nat) := (~ ((real_of_int x0) = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow (real_of_int x0) x1) = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : int) := forall y0 : nat, (~ (x0 = (int_of_num (NUMERAL 0)))) -> ~ ((int_pow x0 y0) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := forall y0 : nat, (~ ((real_of_int x0) = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow (real_of_int x0) y0) = (real_of_num (NUMERAL 0))).
Definition term4 (x0 : nat) := real_of_int (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow y0 y1) = (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term21 := forall y0 : int, forall y1 : nat, (~ (y0 = (int_of_num (NUMERAL 0)))) -> ~ ((int_pow y0 y1) = (int_of_num (NUMERAL 0))).
Definition term13 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term19 (x0 : int) (x1 : nat) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> ~ ((int_pow x0 x1) = (int_of_num (NUMERAL 0))).
Definition term10 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term17 (x0 : int) (x1 : nat) := ~ ((real_pow (real_of_int x0) x1) = (real_of_num (NUMERAL 0))).
Definition term12 (x0 : int) := imp (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term15 (x0 : int) (x1 : nat) := @eq real (real_pow (real_of_int x0) x1).
Definition term16 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow x0 x1)).
Definition term7 (x0 : int) := @eq real (real_of_int x0).
Definition term14 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
