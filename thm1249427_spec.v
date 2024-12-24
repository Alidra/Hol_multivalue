Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249427 : forall (d''' : nat) (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add (Nat.add p d) n) = (Nat.add (Nat.add p q) d')), (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add q d'')) = (Nat.add (Nat.add p q) d').
