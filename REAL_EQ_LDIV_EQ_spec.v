Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1629489 : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (NUMERAL 0)) z) -> ((real_div x z) = y) = (x = (real_mul y z)).