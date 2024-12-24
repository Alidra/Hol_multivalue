Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248992 : forall (d''' : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : p = (Nat.add n d'')) (h3 : (Nat.add p d) = (Nat.add n d')), (Nat.add (Nat.add n d'') (Nat.add (Nat.add d' d'') (S d'''))) = (Nat.add n d').
