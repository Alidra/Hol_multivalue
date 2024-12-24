Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := int_of_num (NUMERAL 0).
Definition term5 := ~ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term3 := S (Nat.add 0 0).
Definition term4 := (((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))) = False) -> ~ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term0 := int_of_num (NUMERAL (BIT1 0)).
Definition term2 := NUMERAL (BIT1 0).
