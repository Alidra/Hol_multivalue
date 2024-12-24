Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem207311 : (forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.add (Nat.mul m n) p) n) = (Nat.modulo p n)) /\ ((forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.add (Nat.mul n m) p) n) = (Nat.modulo p n)) /\ ((forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.add p (Nat.mul m n)) n) = (Nat.modulo p n)) /\ (forall m : nat, forall n : nat, forall p : nat, (Nat.modulo (Nat.add p (Nat.mul n m)) n) = (Nat.modulo p n)))).
