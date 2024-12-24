Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1367839 : forall (x : nat) (n : nat), ((real_pow (real_of_num x) n) = (real_of_num (Nat.pow x n))) /\ ((real_pow (real_neg (real_of_num x)) n) = (@COND real (Coq.Arith.PeanoNat.Nat.Even n) (real_of_num (Nat.pow x n)) (real_neg (real_of_num (Nat.pow x n))))).
