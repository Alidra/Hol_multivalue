Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term2 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> False.
