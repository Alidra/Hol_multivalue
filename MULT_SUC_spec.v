Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem81331 : forall m : nat, forall n : nat, (Nat.mul m (S n)) = (Nat.add m (Nat.mul m n)).
