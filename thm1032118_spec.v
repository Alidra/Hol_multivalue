Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032118 : forall (y : nat) (x : nat) (z : nat), (Nat.mul x (Nat.add y z)) = (Nat.add (Nat.mul x y) (Nat.mul x z)).
