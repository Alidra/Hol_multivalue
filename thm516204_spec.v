Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516204 : ((Nat.pow 0 0) = (BIT1 0)) /\ ((forall m : nat, (Nat.pow (BIT0 m) 0) = (BIT1 0)) /\ ((forall m : nat, (Nat.pow (BIT1 m) 0) = (BIT1 0)) /\ ((forall n : nat, (Nat.pow 0 (BIT0 n)) = (Nat.mul (Nat.pow 0 n) (Nat.pow 0 n))) /\ ((forall m : nat, forall n : nat, (Nat.pow (BIT0 m) (BIT0 n)) = (Nat.mul (Nat.pow (BIT0 m) n) (Nat.pow (BIT0 m) n))) /\ ((forall m : nat, forall n : nat, (Nat.pow (BIT1 m) (BIT0 n)) = (Nat.mul (Nat.pow (BIT1 m) n) (Nat.pow (BIT1 m) n))) /\ ((forall n : nat, (Nat.pow 0 (BIT1 n)) = 0) /\ ((forall m : nat, forall n : nat, (Nat.pow (BIT0 m) (BIT1 n)) = (Nat.mul (BIT0 m) (Nat.mul (Nat.pow (BIT0 m) n) (Nat.pow (BIT0 m) n)))) /\ (forall m : nat, forall n : nat, (Nat.pow (BIT1 m) (BIT1 n)) = (Nat.mul (BIT1 m) (Nat.mul (Nat.pow (BIT1 m) n) (Nat.pow (BIT1 m) n))))))))))).
