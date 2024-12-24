Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1669003 : forall n : nat, forall x : real, forall y : real, ((real_pow x n) = (real_pow y n)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even n) ((n = (NUMERAL 0)) \/ ((real_abs x) = (real_abs y))) (x = y)).
