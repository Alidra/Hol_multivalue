Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302004 : forall x : int, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (int_pow (int_abs x) n) = (int_pow x n).
