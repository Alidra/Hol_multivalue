Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1646031 : forall x : real, forall y : real, ((real_abs x) = (real_abs y)) = ((real_pow x (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y (NUMERAL (BIT0 (BIT1 0))))).
