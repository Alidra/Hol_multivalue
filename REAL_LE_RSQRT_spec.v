Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1961031 : forall x : real, forall y : real, (real_le (real_pow x (NUMERAL (BIT0 (BIT1 0)))) y) -> real_le x (sqrt y).
