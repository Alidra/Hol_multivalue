Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term1 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) x0.
