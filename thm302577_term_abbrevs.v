Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y2) = (Nat.add y1 y2)) = (y0 = y1)) x0.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1)) x2.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0)) x1.
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0).
