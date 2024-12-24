Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT1 y1)) = (BIT0 (S (Nat.add y0 y1)))).
Definition term1 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1)).
Definition term3 (x0 : nat) := forall y0 : nat, (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0)).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (BIT1 y0) (BIT0 y1)) = (BIT1 (Nat.add y0 y1))) x0.
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0))) x1.
