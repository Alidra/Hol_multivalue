Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := real_of_num (NUMERAL 0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term1 := real_neg (real_of_num (NUMERAL 0)).
Definition term3 := (~ ((real_neg (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> False.
