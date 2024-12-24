Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307928 : forall x : int, forall n : nat, ((int_pow x n) = (int_of_num (NUMERAL (BIT1 0)))) = ((((int_abs x) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_lt x (int_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even n)) \/ (n = (NUMERAL 0))).
