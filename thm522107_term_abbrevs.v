Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y0) = y1) x0.
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) x0) = y0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
