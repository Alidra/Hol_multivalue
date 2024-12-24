Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249021 : forall (d''' : nat) (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : (Nat.add (Nat.add p d) d') = (Nat.add p d'')), (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) d') = (Nat.add p d'').
