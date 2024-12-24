Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := BIT1 (Nat.add x0 x1).
Definition term3 := BIT1 (Nat.add (BIT1 0) 0).
Definition term2 := Nat.add (BIT0 (BIT1 0)) (BIT1 0).
Definition term0 (x0 : nat) (x1 : nat) := Nat.add (BIT0 x0) (BIT1 x1).
