Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305812 : forall x : int, (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x) = (int_add x x).
