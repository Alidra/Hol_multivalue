Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := real_of_num (NUMERAL (BIT1 0)).
Definition term0 := real_inv (real_of_num (NUMERAL (BIT1 0))).