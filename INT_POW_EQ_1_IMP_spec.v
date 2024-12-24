Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307966 : forall x : int, forall n : nat, ((~ (n = (NUMERAL 0))) /\ ((int_pow x n) = (int_of_num (NUMERAL (BIT1 0))))) -> (int_abs x) = (int_of_num (NUMERAL (BIT1 0))).
