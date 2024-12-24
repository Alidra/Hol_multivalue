Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032092 : forall (a : nat) (b : nat) (c : nat), (Nat.add (Nat.add a b) c) = (Nat.add a (Nat.add b c)).
