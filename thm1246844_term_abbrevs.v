Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := x0 (dist (@pair nat nat x1 x2)).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> x2 y0) /\ ((x0 = (Nat.add x1 y0)) -> x2 y0).
