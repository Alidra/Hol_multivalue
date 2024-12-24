Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1383497 : forall x : real, (real_pow x (NUMERAL (BIT0 (BIT1 0)))) = (real_mul x x).
