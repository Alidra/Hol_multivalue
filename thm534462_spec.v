Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem534462 : (forall n : nat, (Nat.add 0 (BIT0 n)) = (BIT0 n)) /\ ((forall n : nat, (Nat.add 0 (BIT1 n)) = (BIT1 n)) /\ ((forall n : nat, (Nat.add (BIT0 n) 0) = (BIT0 n)) /\ ((forall n : nat, (Nat.add (BIT1 n) 0) = (BIT1 n)) /\ ((forall m : nat, forall n : nat, (Nat.add (BIT0 m) (BIT0 n)) = (BIT0 (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (BIT0 m) (BIT1 n)) = (BIT1 (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (Nat.add (BIT1 m) (BIT0 n)) = (BIT1 (Nat.add m n))) /\ (forall m : nat, forall n : nat, (Nat.add (BIT1 m) (BIT1 n)) = (BIT0 (S (Nat.add m n)))))))))).
