Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247613 : forall (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), (Nat.add m n) = (Nat.add (Nat.add p q) d).
