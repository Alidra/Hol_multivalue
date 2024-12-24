Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032094 : forall (c : nat) (a : nat) (d : nat), (Nat.add a (Nat.add c d)) = (Nat.add c (Nat.add a d)).
