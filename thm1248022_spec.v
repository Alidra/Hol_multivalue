Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248022 : forall (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (Nat.add (Nat.add m n) d)), (Nat.add p (Nat.add n d'')) = (Nat.add (Nat.add (Nat.add p d') n) d).
