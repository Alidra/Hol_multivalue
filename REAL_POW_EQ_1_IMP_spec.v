Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1653669 : forall x : real, forall n : nat, ((~ (n = (NUMERAL 0))) /\ ((real_pow x n) = (real_of_num (NUMERAL (BIT1 0))))) -> (real_abs x) = (real_of_num (NUMERAL (BIT1 0))).
