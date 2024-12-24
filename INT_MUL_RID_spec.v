Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306233 : forall x : int, (int_mul x (int_of_num (NUMERAL (BIT1 0)))) = x.
