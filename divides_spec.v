Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3074597 : forall (b : nat) (a : nat), (num_divides a b) = (exists x : nat, b = (Nat.mul a x)).
