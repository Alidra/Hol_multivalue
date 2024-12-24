Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) (x1 : nat) := BIT1 (Nat.add x0 x1).
Definition term1 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT0 x1).
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT1 x0) (BIT0 y0)) = (BIT1 (Nat.add x0 y0))) x1.
