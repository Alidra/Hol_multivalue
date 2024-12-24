Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2447244 : forall (x : int) (y : int), ((fun y' : int => ((x = (int_of_num (NUMERAL 0))) \/ (y' = (int_of_num (NUMERAL 0)))) = ((int_mul x y') = (int_of_num (NUMERAL 0)))) y) = (((x = (int_of_num (NUMERAL 0))) \/ (y = (int_of_num (NUMERAL 0)))) = ((int_mul x y) = (int_of_num (NUMERAL 0)))).
