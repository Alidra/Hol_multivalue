Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2746101 : forall n : int, forall k : nat, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow n k)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) n) /\ (~ (k = (NUMERAL 0)))).
