Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
