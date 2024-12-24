Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247842 : forall (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), (Nat.add m (Nat.add q d'')) = (Nat.add (Nat.add (Nat.add m d') q) d).
