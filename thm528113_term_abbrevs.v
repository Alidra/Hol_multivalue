Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0)) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT1 y1)) = (BIT1 (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1))))))).
