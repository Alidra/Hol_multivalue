Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2595338 : forall n : int, (div n (int_of_num (NUMERAL (BIT1 0)))) = n.
