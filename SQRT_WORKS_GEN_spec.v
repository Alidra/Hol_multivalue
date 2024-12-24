Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1919069 : forall x : real, ((real_sgn (sqrt x)) = (real_sgn x)) /\ ((real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x)).
