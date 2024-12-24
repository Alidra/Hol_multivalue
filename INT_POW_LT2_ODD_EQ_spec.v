Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308561 : forall n : nat, forall x : int, forall y : int, (Coq.Arith.PeanoNat.Nat.Odd n) -> (int_lt (int_pow x n) (int_pow y n)) = (int_lt x y).
