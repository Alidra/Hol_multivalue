Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248348 : forall (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add p q) = (Nat.add (Nat.add (Nat.add p d) n) d')), (Nat.add p (Nat.add n d'')) = (Nat.add (Nat.add (Nat.add p d) n) d').
