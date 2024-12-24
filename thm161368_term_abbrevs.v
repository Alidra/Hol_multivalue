Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0.
