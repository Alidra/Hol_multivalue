Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249601 : forall (d''' : nat) (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add (Nat.add m d) q) = (Nat.add (Nat.add m n) d')), (Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) q) = (Nat.add (Nat.add m (Nat.add q d'')) d').
