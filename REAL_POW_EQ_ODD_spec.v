Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1666511 : forall n : nat, forall x : real, forall y : real, ((Coq.Arith.PeanoNat.Nat.Odd n) /\ ((real_pow x n) = (real_pow y n))) -> x = y.
