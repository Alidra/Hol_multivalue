Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515544 : (forall m : nat, forall n : nat, (Nat.mul (NUMERAL m) (NUMERAL n)) = (NUMERAL (Nat.mul m n))) /\ (((Nat.mul 0 0) = 0) /\ ((forall n : nat, (Nat.mul 0 (BIT0 n)) = 0) /\ ((forall n : nat, (Nat.mul 0 (BIT1 n)) = 0) /\ ((forall n : nat, (Nat.mul (BIT0 n) 0) = 0) /\ ((forall n : nat, (Nat.mul (BIT1 n) 0) = 0) /\ ((forall m : nat, forall n : nat, (Nat.mul (BIT0 m) (BIT0 n)) = (BIT0 (BIT0 (Nat.mul m n)))) /\ ((forall m : nat, forall n : nat, (Nat.mul (BIT0 m) (BIT1 n)) = (Nat.add (BIT0 m) (BIT0 (BIT0 (Nat.mul m n))))) /\ ((forall m : nat, forall n : nat, (Nat.mul (BIT1 m) (BIT0 n)) = (Nat.add (BIT0 n) (BIT0 (BIT0 (Nat.mul m n))))) /\ (forall m : nat, forall n : nat, (Nat.mul (BIT1 m) (BIT1 n)) = (Nat.add (BIT1 m) (Nat.add (BIT0 n) (BIT0 (BIT0 (Nat.mul m n)))))))))))))).
