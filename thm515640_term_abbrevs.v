Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.add y1 y2)) = (Nat.mul (Nat.pow y0 y1) (Nat.pow y0 y2))) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1))) x1.
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.add y0 y1)) = (Nat.mul (Nat.pow x0 y0) (Nat.pow x0 y1)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x1 (Nat.add x0 y0)) = (Nat.mul (Nat.pow x1 x0) (Nat.pow x1 y0))) x2.
