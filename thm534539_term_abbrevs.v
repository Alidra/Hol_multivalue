Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := BIT0 (S x0).
Definition term2 := S (Nat.add (BIT1 0) 0).
Definition term8 := BIT0 (S (Nat.add (BIT1 0) 0)).
Definition term1 := Nat.add (BIT1 0) 0.
Definition term4 (x0 : nat) := S (BIT1 x0).
Definition term6 := BIT0 (S 0).
Definition term0 (x0 : nat) := Nat.add (BIT1 x0) 0.
Definition term9 := BIT0 (BIT0 (BIT1 0)).
Definition term7 := BIT0 (BIT1 0).
Definition term3 := S (BIT1 0).
