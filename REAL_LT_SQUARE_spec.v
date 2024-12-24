Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1630933 : forall x : real, (real_lt (real_of_num (NUMERAL 0)) (real_mul x x)) = (~ (x = (real_of_num (NUMERAL 0)))).
