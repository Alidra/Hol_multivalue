Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309981 : forall x : int, (int_sgn (int_pow x (NUMERAL (BIT0 (BIT1 0))))) = (int_sgn (int_abs x)).
