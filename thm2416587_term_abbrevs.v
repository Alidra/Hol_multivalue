Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := (fun y0 : int => (int_neg y0) = (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) x0.
Definition term0 := forall y0 : int, (int_neg y0) = (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term2 (x0 : int) := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0.
