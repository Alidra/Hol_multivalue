Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2257146 : forall x : real, (real_div (real_div x (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x))) (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_abs (real_div x (real_add (real_of_num (NUMERAL (BIT1 0))) (real_abs x)))))) = x.
