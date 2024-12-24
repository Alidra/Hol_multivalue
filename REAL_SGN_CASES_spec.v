Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1740648 : forall x : real, ((real_sgn x) = (real_of_num (NUMERAL 0))) \/ (((real_sgn x) = (real_of_num (NUMERAL (BIT1 0)))) \/ ((real_sgn x) = (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
