Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416573 : forall (x : int), (int_mul x x) = (int_pow x (NUMERAL (BIT0 (BIT1 0)))).
