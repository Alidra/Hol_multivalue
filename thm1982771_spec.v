Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982771 : forall (x : real), (real_mul x x) = (real_pow x (NUMERAL (BIT0 (BIT1 0)))).
