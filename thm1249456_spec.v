Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249456 : forall (d''' : nat) (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add (Nat.add p d) n) = (Nat.add (Nat.add p q) d')), (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) n) = (Nat.add (Nat.add p (Nat.add n d'')) d').
