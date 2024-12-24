Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248384 : forall (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (Nat.add (Nat.add m d) q) = (Nat.add (Nat.add m n) d')), (Nat.add (Nat.add m d) q) = (Nat.add (Nat.add m n) d').
