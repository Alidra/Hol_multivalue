Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248244 : forall (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add (Nat.add p d) n) = (Nat.add (Nat.add p q) d')), (Nat.add (Nat.add p d) (Nat.add q d'')) = (Nat.add (Nat.add p q) d').
