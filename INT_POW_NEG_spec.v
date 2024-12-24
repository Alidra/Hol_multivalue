Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308813 : forall x : int, forall n : nat, (int_pow (int_neg x) n) = (@COND int (Coq.Arith.PeanoNat.Nat.Even n) (int_pow x n) (int_neg (int_pow x n))).
