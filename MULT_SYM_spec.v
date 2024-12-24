Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem81820 : forall m : nat, forall n : nat, (Nat.mul m n) = (Nat.mul n m).
