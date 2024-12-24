Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem79120 : forall (n : nat) (m : nat) (p : nat), ((Nat.add m n) = (Nat.add n m)) /\ (((Nat.add (Nat.add m n) p) = (Nat.add m (Nat.add n p))) /\ ((Nat.add m (Nat.add n p)) = (Nat.add n (Nat.add m p)))).
