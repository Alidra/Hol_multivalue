Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416519 : forall (m : int), (int_add m m) = (int_mul (int_add (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT1 0)))) m).
