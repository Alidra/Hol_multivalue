Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (int_abs y0)) x0.
Definition term1 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs x0).