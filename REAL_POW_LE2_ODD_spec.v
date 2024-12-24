Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1661016 : forall n : nat, forall x : real, forall y : real, ((real_le x y) /\ (Coq.Arith.PeanoNat.Nat.Odd n)) -> real_le (real_pow x n) (real_pow y n).
