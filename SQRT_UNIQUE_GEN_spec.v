Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1921051 : forall x : real, forall y : real, (((real_sgn y) = (real_sgn x)) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x))) -> (sqrt x) = y.
