Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2444031 : forall (x : int) (y : int), ((fun y' : int => (x = y') = ((int_sub x y') = (int_of_num (NUMERAL 0)))) y) = ((x = y) = ((int_sub x y) = (int_of_num (NUMERAL 0)))).
