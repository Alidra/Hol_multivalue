Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (x0 : int) := @eq Prop (int_lt (int_of_num (NUMERAL 0)) (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term5 := real_of_int (int_of_num (NUMERAL 0)).
Definition term4 := real_of_num (NUMERAL 0).
Definition term16 := int_of_num (NUMERAL 0).
Definition term2 (x0 : int) := ~ ((real_of_int x0) = (real_of_num (NUMERAL 0))).
Definition term15 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term22 := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) (int_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (~ (y0 = (int_of_num (NUMERAL 0)))).
Definition term13 (x0 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term6 := real_lt (real_of_num (NUMERAL 0)).
Definition term3 (x0 : nat) := real_of_int (int_of_num x0).
Definition term14 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := real_lt (real_of_num (NUMERAL 0)) (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term0 (x0 : int) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (~ (y0 = (real_of_num (NUMERAL 0))))) (real_of_int x0).
Definition term8 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term7 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term12 := NUMERAL (BIT0 (BIT1 0)).
Definition term21 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term20 (x0 : int) := @eq real (real_of_int x0).
Definition term17 (x0 : int) := int_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term9 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term10 (x0 : int) := real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term11 (x0 : int) := real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term18 (x0 : int) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))))).
