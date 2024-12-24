Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1956353 : forall x : real, ((sqrt x) = (real_of_num (NUMERAL (BIT1 0)))) = (x = (real_of_num (NUMERAL (BIT1 0)))).
