Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416515 : forall (a : int) (m : int), (int_add (int_mul a m) m) = (int_mul (int_add a (int_of_num (NUMERAL (BIT1 0)))) m).