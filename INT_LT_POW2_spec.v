Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304660 : forall n : nat, int_lt (int_of_num (NUMERAL 0)) (int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) n).
