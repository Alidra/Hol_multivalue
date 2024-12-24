Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1760046 : forall x : real, (real_sgn (real_pow x (NUMERAL (BIT0 (BIT1 0))))) = (real_sgn (real_abs x)).
