Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306612 : forall x : int, (int_neg x) = (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x).
