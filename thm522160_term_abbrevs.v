Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0))) x1.
Definition term2 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0)).
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1)).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1))) x0.
