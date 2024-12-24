Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1740125 : (forall x : real, ((real_sgn x) = (real_of_num (NUMERAL 0))) = (x = (real_of_num (NUMERAL 0)))) /\ ((forall x : real, ((real_sgn x) = (real_of_num (NUMERAL (BIT1 0)))) = (real_gt x (real_of_num (NUMERAL 0)))) /\ (forall x : real, ((real_sgn x) = (real_neg (real_of_num (NUMERAL (BIT1 0))))) = (real_lt x (real_of_num (NUMERAL 0))))).
