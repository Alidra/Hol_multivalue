Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309449 : (forall x : int, ((int_sgn x) = (int_of_num (NUMERAL 0))) = (x = (int_of_num (NUMERAL 0)))) /\ ((forall x : int, ((int_sgn x) = (int_of_num (NUMERAL (BIT1 0)))) = (int_gt x (int_of_num (NUMERAL 0)))) /\ (forall x : int, ((int_sgn x) = (int_neg (int_of_num (NUMERAL (BIT1 0))))) = (int_lt x (int_of_num (NUMERAL 0))))).
