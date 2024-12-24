Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309350 : forall x : int, ((int_sgn x) = (int_of_num (NUMERAL 0))) \/ (((int_sgn x) = (int_of_num (NUMERAL (BIT1 0)))) \/ ((int_sgn x) = (int_neg (int_of_num (NUMERAL (BIT1 0)))))).
