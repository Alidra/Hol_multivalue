Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249079 : forall (d''' : nat) (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : n = (Nat.add (Nat.add (Nat.add n d') d) d'')), n = (Nat.add (Nat.add (Nat.add n d') (Nat.add (Nat.add d' d'') (S d'''))) d'').
