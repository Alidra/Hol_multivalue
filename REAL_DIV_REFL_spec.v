Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1593003 : forall x : real, (~ (x = (real_of_num (NUMERAL 0)))) -> (real_div x x) = (real_of_num (NUMERAL (BIT1 0))).
