Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308055 : forall n : nat, forall x : int, forall y : int, ((int_pow x n) = (int_pow y n)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even n) ((n = (NUMERAL 0)) \/ ((int_abs x) = (int_abs y))) (x = y)).