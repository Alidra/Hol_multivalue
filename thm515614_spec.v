Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515614 : (forall n : nat, (Nat.mul 0 n) = 0) /\ ((forall m : nat, (Nat.mul m 0) = 0) /\ ((forall n : nat, (Nat.mul (BIT1 0) n) = n) /\ ((forall m : nat, (Nat.mul m (BIT1 0)) = m) /\ ((forall m : nat, forall n : nat, (Nat.mul (S m) n) = (Nat.add (Nat.mul m n) n)) /\ (forall m : nat, forall n : nat, (Nat.mul m (S n)) = (Nat.add m (Nat.mul m n))))))).
