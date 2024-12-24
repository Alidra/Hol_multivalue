Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : real) := (fun y0 : real => (real_div y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
