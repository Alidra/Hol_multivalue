Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303073 : forall x : int, int_le (int_of_num (NUMERAL 0)) (int_pow x (NUMERAL (BIT0 (BIT1 0)))).
