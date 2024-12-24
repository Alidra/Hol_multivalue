Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249195 : forall (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), (Nat.add (Nat.add p d') (Nat.add q d'')) = (Nat.add (Nat.add p q) (Nat.add (Nat.add d' d'') (S d'''))).
