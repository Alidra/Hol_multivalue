Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem523589 : (forall m : nat, forall n : nat, (Nat.sub (BIT0 m) (BIT0 n)) = (BIT0 (Nat.sub m n))) /\ ((forall m : nat, forall n : nat, (Nat.sub (BIT0 m) (BIT1 n)) = (Nat.pred (BIT0 (Nat.sub m n)))) /\ ((forall m : nat, forall n : nat, (Nat.sub (BIT1 m) (BIT0 n)) = (@COND nat (Peano.le n m) (BIT1 (Nat.sub m n)) 0)) /\ (forall m : nat, forall n : nat, (Nat.sub (BIT1 m) (BIT1 n)) = (BIT0 (Nat.sub m n))))).
