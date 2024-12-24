Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301903 : forall x : int, forall y : int, ((int_abs x) = (int_abs y)) = ((int_pow x (NUMERAL (BIT0 (BIT1 0)))) = (int_pow y (NUMERAL (BIT0 (BIT1 0))))).
