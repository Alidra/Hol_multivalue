Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1660753 : forall n : nat, forall x : real, forall y : real, ((real_lt x y) /\ (Coq.Arith.PeanoNat.Nat.Odd n)) -> real_lt (real_pow x n) (real_pow y n).
