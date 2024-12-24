Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1669140 : forall x : real, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (real_pow (real_abs x) n) = (real_pow x n).
