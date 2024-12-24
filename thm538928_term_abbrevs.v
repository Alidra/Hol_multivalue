Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 := BIT0 (Nat.add (BIT0 (BIT1 0)) (BIT0 (BIT0 (BIT1 0)))).
Definition term6 (x0 : nat) (x1 : nat) := BIT1 (Nat.add x0 x1).
Definition term0 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT0 x1).
Definition term7 := Nat.add (BIT1 0) (BIT0 (BIT1 0)).
Definition term8 := BIT1 (Nat.add 0 (BIT1 0)).
Definition term5 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT0 x1).
Definition term2 := Nat.add (BIT0 (BIT1 0)) (BIT0 (BIT0 (BIT1 0))).
Definition term9 (x0 : nat) := Nat.add 0 (BIT1 x0).
Definition term12 := BIT0 (BIT1 (BIT1 0)).
Definition term11 := BIT1 (BIT1 0).
Definition term3 := BIT0 (Nat.add (BIT1 0) (BIT0 (BIT1 0))).
Definition term10 := Nat.add 0 (BIT1 0).
Definition term4 := BIT0 (BIT1 0).
Definition term1 (x0 : nat) (x1 : nat) := BIT0 (Nat.add x0 x1).
Definition term14 := BIT0 (BIT0 (BIT1 (BIT1 0))).
