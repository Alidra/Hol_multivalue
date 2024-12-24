Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247290 : forall (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')), (Nat.add p d) = (Nat.add n d').
