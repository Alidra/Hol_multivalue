Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513549 : forall n : nat, (Nat.pred (Nat.add n n)) = (@COND nat (n = 0) 0 (S (Nat.add (Nat.pred n) (Nat.pred n)))).
