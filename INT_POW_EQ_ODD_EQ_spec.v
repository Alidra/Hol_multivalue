Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308119 : forall n : nat, forall x : int, forall y : int, (Coq.Arith.PeanoNat.Nat.Odd n) -> ((int_pow x n) = (int_pow y n)) = (x = y).
