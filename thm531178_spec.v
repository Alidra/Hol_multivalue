Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem531178 : (forall m : nat, forall n : nat, (Nat.add (BIT1 m) (BIT0 n)) = (BIT1 (Nat.add m n))) /\ (forall m : nat, forall n : nat, (Nat.add (BIT1 m) (BIT1 n)) = (BIT0 (S (Nat.add m n)))).
