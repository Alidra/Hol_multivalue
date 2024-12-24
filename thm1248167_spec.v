Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248167 : forall (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (Nat.add (Nat.add p d) n) = (Nat.add (Nat.add p q) d')), (Nat.add (Nat.add p d) n) = (Nat.add (Nat.add p q) d').
