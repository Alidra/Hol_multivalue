Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2227384 : forall x : real, forall y : real, ((real_div x (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x))) = (real_div y (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs y)))) = (x = y).