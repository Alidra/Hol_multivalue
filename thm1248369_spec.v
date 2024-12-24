Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248369 : forall (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (Nat.add (Nat.add (Nat.add m d) q) d')), (Nat.add m n) = (Nat.add (Nat.add (Nat.add m d) q) d').
