Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249224 : forall (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), (Nat.add (Nat.add p d') n) = (Nat.add (Nat.add p (Nat.add n d'')) (Nat.add (Nat.add d' d'') (S d'''))).
