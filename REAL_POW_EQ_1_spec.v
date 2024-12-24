Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1657725 : forall x : real, forall n : nat, ((real_pow x n) = (real_of_num (NUMERAL (BIT1 0)))) = ((((real_abs x) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt x (real_of_num (NUMERAL 0))) -> Coq.Arith.PeanoNat.Nat.Even n)) \/ (n = (NUMERAL 0))).
