Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307740 : forall x : int, (int_pow x (NUMERAL (BIT0 (BIT1 0)))) = (int_mul x x).
