Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247766 : forall (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), (Nat.add (Nat.add p d') (Nat.add q d'')) = (Nat.add (Nat.add p q) d).
