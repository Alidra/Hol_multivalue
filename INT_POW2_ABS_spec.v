Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307610 : forall x : int, (int_pow (int_abs x) (NUMERAL (BIT0 (BIT1 0)))) = (int_pow x (NUMERAL (BIT0 (BIT1 0)))).
