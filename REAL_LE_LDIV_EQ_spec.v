Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1628775 : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (NUMERAL 0)) z) -> (real_le (real_div x z) y) = (real_le x (real_mul y z)).