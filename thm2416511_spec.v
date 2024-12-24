Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416511 : forall (x : int), (int_mul (int_of_num (NUMERAL (BIT1 0))) x) = x.
