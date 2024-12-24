Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247718 : forall (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), (Nat.add m n) = (Nat.add (Nat.add (Nat.add m d') q) d).
