Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := Nat.add (BIT1 0) 0.
Definition term2 := BIT1 (Nat.add (BIT1 0) 0).
Definition term0 (x0 : nat) := Nat.add (BIT1 x0) 0.
Definition term3 := BIT1 (BIT1 0).
