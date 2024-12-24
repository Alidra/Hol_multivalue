Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1593153 : forall x : real, forall y : real, (~ (y = (real_of_num (NUMERAL 0)))) -> (real_mul (real_div x y) y) = x.
