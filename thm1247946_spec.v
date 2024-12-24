Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247946 : forall (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (Nat.add (Nat.add m n) d)), (Nat.add (Nat.add m d') q) = (Nat.add (Nat.add m n) d).
