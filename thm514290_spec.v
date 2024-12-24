Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem514290 : (forall m : nat, forall n : nat, (Nat.add m n) = (Nat.add m n)) /\ ((0 = 0) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall n : nat, (Nat.add n n) = (Nat.add n n)) /\ ((forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))) /\ (forall m : nat, forall n : nat, (Nat.add (Nat.add m m) (Nat.add n n)) = (Nat.add (Nat.add m n) (Nat.add m n))))))))))).
