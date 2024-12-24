Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1636868 : forall n : nat, forall x : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ (real_le x (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow x n) (real_of_num (NUMERAL (BIT1 0))).
