Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249485 : forall (d''' : nat) (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (Nat.add (Nat.add (Nat.add p d) n) d')), (Nat.add p q) = (Nat.add (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add q d'')) d').
