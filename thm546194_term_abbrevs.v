Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := Nat.add (BIT1 x0) (BIT1 x1).
Definition term2 (x0 : nat) (x1 : nat) := BIT0 (S (Nat.add x0 x1)).
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (BIT1 x0) (BIT1 y0)) = (BIT0 (S (Nat.add x0 y0)))) x1.
