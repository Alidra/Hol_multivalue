Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := real_of_int (int_of_num (NUMERAL 0)).
Definition term1 := real_of_num (NUMERAL 0).
Definition term12 := int_of_num (NUMERAL 0).
Definition term3 := real_lt (real_of_num (NUMERAL 0)).
Definition term0 (x0 : nat) := real_of_int (int_of_num x0).
Definition term10 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term8 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term9 := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term4 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term11 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term6 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term13 := int_of_num (NUMERAL (BIT1 0)).
Definition term7 := NUMERAL (BIT1 0).
