Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1362863 : forall x : real, forall n : nat, (real_pow (real_neg x) n) = (@COND real (Coq.Arith.PeanoNat.Nat.Even n) (real_pow x n) (real_neg (real_pow x n))).
