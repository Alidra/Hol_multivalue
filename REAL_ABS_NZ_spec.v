Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1534492 : forall x : real, (~ (x = (real_of_num (NUMERAL 0)))) = (real_lt (real_of_num (NUMERAL 0)) (real_abs x)).