Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 := BIT0 (Nat.add (BIT1 0) (BIT1 0)).
Definition term2 (x0 : nat) := forall y0 : nat, (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0)).
Definition term4 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT0 x1).
Definition term6 := Nat.add (BIT0 (BIT1 0)) (BIT0 (BIT1 0)).
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1)).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT0 x0) (BIT0 y0)) = (BIT0 (Nat.add x0 y0))) x1.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (BIT0 y0) (BIT0 y1)) = (BIT0 (Nat.add y0 y1))) x0.
Definition term5 (x0 : nat) (x1 : nat) := BIT0 (Nat.add x0 x1).