Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249108 : forall (d''' : nat) (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : (Nat.add (Nat.add n d') d) = (Nat.add n d'')), (Nat.add (Nat.add n d') (Nat.add (Nat.add d' d'') (S d'''))) = (Nat.add n d'').
